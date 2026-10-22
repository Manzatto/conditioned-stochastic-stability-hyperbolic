module

public import LeanShared.Analysis.ScalarCoefficientResolvent
public import LeanShared.Analysis.RieszContourEigenvectors
public import LeanShared.Analysis.CompactTwoNormDiscreteSpectrum
public import LeanShared.Analysis.CompactTwoNormMeromorphicResolvent
public import LeanShared.Analysis.TwoNormPeripheralEigenvectors
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity
import Mathlib.Tactic.Linarith

/-! Scalar coefficient growth, dense regular inputs, and separating tests
exclude every isolated spectral value above the coefficient rate. The
proof integrates the analytic scalar continuation around the actual small
Riesz contour, avoiding an assumed operator-norm growth bound. -/

public noncomputable section
open Set Metric ContinuousLinearMap
open scoped Topology

namespace LeanShared.ScalarCoefficientSpectralExclusion
open ScalarCoefficientResolvent

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  (P : H →L[ℂ] H)

/-- Analytic scalar continuation forces every sufficiently small contour
coefficient to vanish, including when the center lies in the spectrum. -/
theorem pairing_projector_eq_zero (ℓ : H →L[ℂ] ℂ) (x : H)
    (C R : ℝ) (positive : 0 < R)
    (growth : ∀ n, ‖ℓ ((P ^ n) x)‖ ≤ C * R ^ n)
    (meromorphic : MeromorphicOn (resolvent P) {z : ℂ | R < ‖z‖})
    (z : ℂ) (r : ℝ) (positiveR : 0 ≤ r)
    (circle : sphere z r ⊆ resolventSet ℂ P)
    (exterior : closedBall z r ⊆ {w : ℂ | R < ‖w‖}) :
    ℓ (RieszContourIdempotent.projector P z r x) = 0 := by
  have integrable : CircleIntegrable (resolvent P) z r :=
    ((AnalyticResolvent.analyticOnNhd P).continuousOn.mono circle).circleIntegrable positiveR
  have mapped := ContourProjectorContinuity.map_circleIntegral
    (ℓ.comp (ContinuousLinearMap.apply ℂ H x)) (resolvent P) z r integrable
  change ℓ ((∮ w in C(z, r), resolvent P w) x) =
    ∮ w in C(z, r), ℓ ((resolvent P w) x) at mapped
  have equalIntegral : (∮ w in C(z, r), ℓ ((resolvent P w) x)) =
      ∮ w in C(z, r), value (fun n => ℓ ((P ^ n) x)) w := by
    apply circleIntegral.integral_congr positiveR
    intro w hw
    exact eq_on_resolvent P ℓ x C R positive growth meromorphic w
      (exterior (sphere_subset_closedBall hw)) (circle hw)
  have analytic (w : ℂ) (hw : w ∈ closedBall z r) :=
    analyticAt_value (fun n => ℓ ((P ^ n) x)) C R positive growth w (exterior hw)
  have integralZero := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    positiveR countable_empty
    (fun w hw => (analytic w hw).continuousAt.continuousWithinAt)
    (fun w hw => (analytic w (ball_subset_closedBall hw.1)).differentiableAt)
  change ℓ (((2 * Real.pi * Complex.I : ℂ)⁻¹ •
    (∮ w in C(z, r), resolvent P w)) x) = 0
  rw [smul_apply, map_smul, mapped, equalIntegral, integralZero, smul_zero]

/-- Dense regular inputs and separating full tests turn scalar contour
vanishing into a zero projector on the complete native carrier. -/
theorem projector_eq_zero {I J : Type*} (seed : I → H) (dense : DenseRange seed)
    (test : J → H →L[ℂ] ℂ)
    (separating : ∀ v : H, (∀ j, test j v = 0) → v = 0)
    (R : ℝ) (positive : 0 < R)
    (growth : ∀ i j, ∃ C : ℝ, ∀ n, ‖test j ((P ^ n) (seed i))‖ ≤ C * R ^ n)
    (meromorphic : MeromorphicOn (resolvent P) {z : ℂ | R < ‖z‖})
    (z : ℂ) (r : ℝ) (positiveR : 0 ≤ r)
    (circle : sphere z r ⊆ resolventSet ℂ P)
    (exterior : closedBall z r ⊆ {w : ℂ | R < ‖w‖}) :
    RieszContourIdempotent.projector P z r = 0 := by
  ext v
  apply separating
  intro j
  apply dense.induction_on (p := fun v => test j (RieszContourIdempotent.projector P z r v) = 0) v
    (isClosed_eq ((test j).comp (RieszContourIdempotent.projector P z r)).continuous
      continuous_const)
  intro i
  obtain ⟨C, bound⟩ := growth i j
  exact pairing_projector_eq_zero P (test j) (seed i) C R positive bound
    meromorphic z r positiveR circle exterior

/-- The compact two-norm hypotheses turn every exterior spectral value
into an eigenvalue; the zero scalar contour then rules it out. -/
theorem not_mem_spectrum {W I J : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (weak : H →L[ℂ] W) (compact : IsCompactOperator weak)
    (α B C D : ℝ) (hα : 0 ≤ α) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n v, ‖(P ^ n) v‖ ≤ C * α ^ n * ‖v‖ + D * B ^ n * ‖weak v‖)
    (seed : I → H) (dense : DenseRange seed) (test : J → H →L[ℂ] ℂ)
    (separating : ∀ v : H, (∀ j, test j v = 0) → v = 0)
    (R : ℝ) (positive : 0 < R) (rate : α ≤ R)
    (growth : ∀ i j, ∃ C : ℝ, ∀ n, ‖test j ((P ^ n) (seed i))‖ ≤ C * R ^ n)
    (z : ℂ) (outside : R < ‖z‖) : z ∉ spectrum ℂ P := by
  intro spectral
  obtain ⟨v, nonzero, eigen⟩ := CompactTwoNormFredholm.eigenvector_of_mem_spectrum
    P weak compact α B C D hα hB hC hD estimate z (rate.trans_lt outside) spectral
  obtain ⟨r, positiveR, punctured⟩ := CompactTwoNormDiscreteSpectrum.punctured_resolvent
    P weak compact α B C D hα hB hC hD estimate z (rate.trans_lt outside)
  let d := min r (‖z‖ - R) / 2
  have positiveD : 0 < d := half_pos (lt_min positiveR (sub_pos.mpr outside))
  have smallR : d < r := (half_lt_self (lt_min positiveR (sub_pos.mpr outside))).trans_le
    (min_le_left _ _)
  have smallGap : d < ‖z‖ - R :=
    (half_lt_self (lt_min positiveR (sub_pos.mpr outside))).trans_le (min_le_right _ _)
  have circle : sphere z d ⊆ resolventSet ℂ P := by
    intro w hw
    apply punctured
    refine ⟨?_, ?_⟩
    · exact (show dist w z = d from hw).trans_lt smallR
    · intro equal
      have same : w = z := mem_singleton_iff.mp equal
      subst w
      have hzero : (0 : ℝ) = d := by simpa only [mem_sphere, dist_self] using hw
      exact positiveD.ne' hzero.symm
  have exterior : closedBall z d ⊆ {w : ℂ | R < ‖w‖} := by
    intro w hw
    have close : ‖w - z‖ ≤ d := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have triangle : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      simpa only [add_sub_cancel, norm_sub_rev] using norm_add_le w (z - w)
    change R < ‖w‖
    linarith
  have meromorphic : MeromorphicOn (resolvent P) {w : ℂ | R < ‖w‖} :=
    fun w hw => CompactTwoNormMeromorphicResolvent.meromorphicAt P weak compact
      α B C D hα hB hC hD estimate w (rate.trans_lt hw)
  have zero := projector_eq_zero P seed dense test separating R positive growth
    meromorphic z d positiveD.le circle exterior
  have fixed := RieszContourIdempotent.projector_eigenvector P z z d positiveD circle
    (mem_ball_self positiveD) v eigen
  apply nonzero
  rw [zero, zero_apply] at fixed
  exact fixed.symm

/-- The resulting bound controls the whole spectral radius, with constants
allowed to depend on each regular input and each separating test. -/
theorem spectralRadius_le {W I J : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (weak : H →L[ℂ] W) (compact : IsCompactOperator weak)
    (α B C D : ℝ) (hα : 0 ≤ α) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n v, ‖(P ^ n) v‖ ≤ C * α ^ n * ‖v‖ + D * B ^ n * ‖weak v‖)
    (seed : I → H) (dense : DenseRange seed) (test : J → H →L[ℂ] ℂ)
    (separating : ∀ v : H, (∀ j, test j v = 0) → v = 0)
    (R : ℝ) (positive : 0 < R) (rate : α ≤ R)
    (growth : ∀ i j, ∃ C : ℝ, ∀ n, ‖test j ((P ^ n) (seed i))‖ ≤ C * R ^ n) :
    spectralRadius ℂ P ≤ ENNReal.ofReal R := by
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le (fun z hz => ?_)
  have bound : ‖z‖ ≤ R := le_of_not_gt (fun outside =>
    not_mem_spectrum P weak compact α B C D hα hB hC hD estimate seed dense test separating
      R positive rate growth z outside hz)
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal bound

/-- Arbitrarily small exponential losses are sufficient: no uniform
constant across losses, regular inputs, or full tests is required. -/
theorem spectralRadius_le_of_forall_gt {W I J : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (weak : H →L[ℂ] W) (compact : IsCompactOperator weak)
    (α B C D : ℝ) (hα : 0 ≤ α) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n v, ‖(P ^ n) v‖ ≤ C * α ^ n * ‖v‖ + D * B ^ n * ‖weak v‖)
    (seed : I → H) (dense : DenseRange seed) (test : J → H →L[ℂ] ℂ)
    (separating : ∀ v : H, (∀ j, test j v = 0) → v = 0)
    (R : ℝ) (positive : 0 < R) (rate : α ≤ R)
    (growth : ∀ R' : ℝ, R < R' → ∀ i j, ∃ C : ℝ,
      ∀ n, ‖test j ((P ^ n) (seed i))‖ ≤ C * R' ^ n) :
    spectralRadius ℂ P ≤ ENNReal.ofReal R := by
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le (fun z hz => ?_)
  have bound : ‖z‖ ≤ R := by
    by_contra! large
    let R' := (R + ‖z‖) / 2
    have above : R < R' := by dsimp only [R']; linarith
    have below : R' < ‖z‖ := by dsimp only [R']; linarith
    exact not_mem_spectrum P weak compact α B C D hα hB hC hD estimate seed dense test
      separating R' (positive.trans above) (rate.trans above.le) (growth R' above) z below hz
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal bound

end LeanShared.ScalarCoefficientSpectralExclusion
