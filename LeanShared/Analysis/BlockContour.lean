module

public import LeanShared.Analysis.BlockResolvent
public import LeanShared.Analysis.ConjugateResolvent
public import LeanShared.Analysis.RieszContourIdempotent
public import LeanShared.Analysis.ContourProjectorContinuity
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity

/-! Exact direct-sum and conjugation formulas for actual Riesz contour projectors. -/

public noncomputable section
open ContinuousLinearMap Metric
namespace LeanShared.BlockContour
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Continuous linear maps commute with normalized contour integration. -/
theorem map_contour (L : E →L[ℂ] F) (f : ℂ → E) (c : ℂ) (r : ℝ)
    (hf : CircleIntegrable f c r) :
    L (ContourProjectorContinuity.contour f c r) =
      ContourProjectorContinuity.contour (fun z => L (f z)) c r := by
  unfold ContourProjectorContinuity.contour
  rw [map_smul, ContourProjectorContinuity.map_circleIntegral L f c r hf]

private theorem integrable_resolvent (A : E →L[ℂ] E) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hA : sphere c r ⊆ resolventSet ℂ A) : CircleIntegrable (resolvent A) c r :=
  (show ContinuousOn (resolvent A) (sphere c r) from fun _ hz =>
    (spectrum.hasDerivAt_resolvent_const_left (hA hz)).continuousAt.continuousWithinAt).circleIntegrable hr

/-- The actual contour projector of a diagonal operator is diagonal with
the two actual block contour projectors. -/
theorem prodMap (A : E →L[ℂ] E) (B : F →L[ℂ] F) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hA : sphere c r ⊆ resolventSet ℂ A)
    (hB : sphere c r ⊆ resolventSet ℂ B) :
    RieszContourIdempotent.projector (A.prodMap B) c r =
      (RieszContourIdempotent.projector A c r).prodMap
        (RieszContourIdempotent.projector B c r) := by
  let f := fun z : ℂ => (resolvent A z, resolvent B z)
  have intA := integrable_resolvent A c r hr hA
  have intB := integrable_resolvent B c r hr hB
  have intPair : CircleIntegrable f c r := by
    exact ⟨intA.1.prodMk intB.1, intA.2.prodMk intB.2⟩
  have pairIntegral : ContourProjectorContinuity.contour f c r =
      (ContourProjectorContinuity.contour (resolvent A) c r,
        ContourProjectorContinuity.contour (resolvent B) c r) := by
    apply Prod.ext
    · exact map_contour (fst ℂ (E →L[ℂ] E) (F →L[ℂ] F)) f c r intPair
    · exact map_contour (snd ℂ (E →L[ℂ] E) (F →L[ℂ] F)) f c r intPair
  have mapped := map_contour (prodMapL ℂ E E F F) f c r intPair
  rw [pairIntegral] at mapped
  simp only [prodMapL_apply] at mapped
  change ContourProjectorContinuity.contour (resolvent (A.prodMap B)) c r =
    (ContourProjectorContinuity.contour (resolvent A) c r).prodMap
      (ContourProjectorContinuity.contour (resolvent B) c r)
  rw [mapped]
  unfold ContourProjectorContinuity.contour
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  exact (BlockResolvent.formula A B z (hA hz) (hB hz)).2

/-- Actual contour projectors transform by continuous conjugation. -/
theorem conjugate (e : E ≃L[ℂ] F) (A : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hA : sphere c r ⊆ resolventSet ℂ A) :
    RieszContourIdempotent.projector (e.conjContinuousAlgEquiv A) c r =
      e.arrowCongr e (RieszContourIdempotent.projector A c r) := by
  have mapped := map_contour (e.arrowCongr e).toContinuousLinearMap
    (resolvent A) c r (integrable_resolvent A c r hr hA)
  change ContourProjectorContinuity.contour (resolvent (e.conjContinuousAlgEquiv A)) c r =
    e.arrowCongr e (ContourProjectorContinuity.contour (resolvent A) c r)
  change e.arrowCongr e (ContourProjectorContinuity.contour (resolvent A) c r) = _ at mapped
  rw [mapped]
  unfold ContourProjectorContinuity.contour
  congr 1
  apply circleIntegral.integral_congr hr
  intro z _
  exact ConjugateResolvent.formula e A z

end LeanShared.BlockContour
