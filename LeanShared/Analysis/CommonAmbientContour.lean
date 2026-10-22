module
public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity
public import Mathlib.Analysis.Normed.Module.Dual

/-! Equality of common ambient resolvents yields equality of actual contour
projector images. Scalar separation avoids any ambient completeness premise. -/
public noncomputable section
open Set Metric
namespace LeanShared.CommonAmbientContour
variable {E F Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem projector_match (P : E →L[ℂ] E) (Q : F →L[ℂ] F)
    (a : E →L[ℂ] Z) (b : F →L[ℂ] Z) (x : E) (y : F)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (resP : sphere c R ⊆ resolventSet ℂ P) (resQ : sphere c R ⊆ resolventSet ℂ Q)
    (common : ∀ z ∈ sphere c R, a ((resolvent P z) x) = b ((resolvent Q z) y)) :
    a ((RieszContourIdempotent.projector P c R) x) =
      b ((RieszContourIdempotent.projector Q c R) y) := by
  have intP : CircleIntegrable (resolvent P) c R :=
    (show ContinuousOn (resolvent P) (sphere c R) from fun _ hz =>
      (spectrum.hasDerivAt_resolvent_const_left (resP hz)).continuousAt.continuousWithinAt).circleIntegrable hR
  have intQ : CircleIntegrable (resolvent Q) c R :=
    (show ContinuousOn (resolvent Q) (sphere c R) from fun _ hz =>
      (spectrum.hasDerivAt_resolvent_const_left (resQ hz)).continuousAt.continuousWithinAt).circleIntegrable hR
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  let left := φ.comp (a.comp (ContinuousLinearMap.apply ℂ E x))
  let right := φ.comp (b.comp (ContinuousLinearMap.apply ℂ F y))
  have mappedP : φ (a ((RieszContourIdempotent.projector P c R) x)) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∮ z in C(c,R), left (resolvent P z)) := by
    change left (ContourProjectorContinuity.contour (resolvent P) c R) = _
    rw [ContourProjectorContinuity.contour, map_smul,
      ContourProjectorContinuity.map_circleIntegral left _ c R intP]
  have mappedQ : φ (b ((RieszContourIdempotent.projector Q c R) y)) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∮ z in C(c,R), right (resolvent Q z)) := by
    change right (ContourProjectorContinuity.contour (resolvent Q) c R) = _
    rw [ContourProjectorContinuity.contour, map_smul,
      ContourProjectorContinuity.map_circleIntegral right _ c R intQ]
  rw [mappedP,mappedQ]
  congr 1
  apply circleIntegral.integral_congr hR
  intro z hz
  exact congrArg φ (common z hz)
end LeanShared.CommonAmbientContour
