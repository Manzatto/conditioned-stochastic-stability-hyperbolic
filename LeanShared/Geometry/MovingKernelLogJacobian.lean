module

public import LeanShared.Analysis.ProjectionKernelTransport
public import LeanShared.Geometry.NormDetFrameRatio
public import LeanShared.Geometry.LogNormDetRegularity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! The genuine logarithmic ratio of moving-kernel Gram volumes has a
smooth expression in a fixed local frame. Projection transport is an
actual polynomial in the two projection operators; no regularity of
moving bases or of a determinant on varying subspaces is assumed. -/
public noncomputable section
namespace LeanShared.MovingKernelLogJacobian
open scoped ContDiff
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

@[expose] def ratio (P : E →L[ℝ] E) (A : E →L[ℝ] F) (B : E →L[ℝ] G) : ℝ :=
  (A.comp P.ker.subtypeL).toLinearMap.normDet / (B.comp P.ker.subtypeL).toLinearMap.normDet

@[expose] def frame (P Q : E →L[ℝ] E) : P.ker →L[ℝ] E :=
  (IntertwiningProjectionTransport.transport P Q).comp P.ker.subtypeL

@[expose] def framedLog (P : E →L[ℝ] E)
    (s : (E →L[ℝ] E) × (E →L[ℝ] F) × (E →L[ℝ] G)) : ℝ :=
  Real.log (s.2.1.comp (frame P s.1)).toLinearMap.normDet -
    Real.log (s.2.2.comp (frame P s.1)).toLinearMap.normDet

theorem log_ratio_eq (P Q : E →L[ℝ] E) (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hp : ∀ v, P (P v) = P v) (hq : ∀ v, Q (Q v) = Q v)
    (small : ‖P - Q‖ * (2 * ‖P‖ + 1) < 1)
    (injectiveA : Function.Injective (A.comp Q.ker.subtypeL))
    (injectiveB : Function.Injective (B.comp Q.ker.subtypeL)) :
    Real.log (ratio Q A B) = framedLog P (Q, A, B) := by
  let H := IntertwiningProjectionTransport.kernelEquivalence P Q hp hq small
  exact NormDetFrameRatio.log_eq (A.comp Q.ker.subtypeL) (B.comp Q.ker.subtypeL) H injectiveA injectiveB

set_option maxHeartbeats 1600000 in
theorem framedLog_contDiffAt (P : E →L[ℝ] E) (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hp : ∀ v, P (P v) = P v)
    (injectiveA : Function.Injective (A.comp P.ker.subtypeL))
    (injectiveB : Function.Injective (B.comp P.ker.subtypeL)) :
    ContDiffAt ℝ ∞ (framedLog P) (P, A, B) := by
  let S := (E →L[ℝ] E) × (E →L[ℝ] F) × (E →L[ℝ] G)
  have self : IntertwiningProjectionTransport.transport P P = ContinuousLinearMap.id ℝ E := by
    have same := IntertwiningProjectionTransport.sub_id P P hp
    exact sub_eq_zero.mp (by simpa only [sub_self, ContinuousLinearMap.zero_comp] using same)
  have frameSelf : frame P P = P.ker.subtypeL := by
    unfold frame
    rw [self, ContinuousLinearMap.id_comp]
  have projection : ContDiff ℝ ∞ (fun s : S => s.1) := contDiff_fst
  have first : ContDiff ℝ ∞ (fun s : S => s.2.1) := contDiff_fst.comp contDiff_snd
  have other : ContDiff ℝ ∞ (fun s : S => s.2.2) := contDiff_snd.comp contDiff_snd
  have frameSmooth : ContDiff ℝ ∞ (fun s : S => frame P s.1) :=
    ((projection.clm_comp contDiff_const).add
      ((contDiff_const.sub projection).clm_comp contDiff_const)).clm_comp contDiff_const
  have numerator := first.clm_comp frameSmooth
  have denominator := other.clm_comp frameSmooth
  have injectiveNumerator : Function.Injective (A.comp (frame P P)) := by
    rw [frameSelf]
    exact injectiveA
  have injectiveDenominator : Function.Injective (B.comp (frame P P)) := by
    rw [frameSelf]
    exact injectiveB
  exact ((LogNormDetRegularity.contDiffAt_log_normDet _ injectiveNumerator).comp (P, A, B)
    numerator.contDiffAt).sub
    ((LogNormDetRegularity.contDiffAt_log_normDet _ injectiveDenominator).comp (P, A, B)
      denominator.contDiffAt)

end LeanShared.MovingKernelLogJacobian
