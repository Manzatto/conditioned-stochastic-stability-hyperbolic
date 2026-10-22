module

public import LeanShared.Analysis.ContourMomentNorms
public import LeanShared.Analysis.UniformFamilyWeakResolventBound
public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform strong/weak norm equivalence on actual outer Riesz ranges,
derived from inverse contour moments and Lasota–Yorke growth. -/

public section
open Filter Topology ContinuousLinearMap Metric
namespace LeanShared.UniformRieszRangeCoercivity
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Common two-norm growth and resolvent bounds force uniform range
coercivity for actual Riesz projectors. Inverse moment identities and
idempotence are algebraic facts, not spectral gaps or rank assumptions. -/
theorem exists_bound (i : E →L[ℂ] W) (α M C D Cw a outer L : ℝ)
    (c : ℂ) (r : ℝ)
    (hα : 0 ≤ α) (hM : 0 ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D) (hCw : 0 ≤ Cw)
    (ha : α < a) (houter : 0 ≤ outer) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (lower : ∀ z ∈ sphere c r, a ≤ ‖z‖) (upper : ∀ z ∈ sphere c r, ‖z‖ ≤ outer) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : E →L[ℂ] E,
      (∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * M ^ n * ‖i x‖) →
      (∀ n x, ‖i ((T ^ n) x)‖ ≤ Cw * M ^ n * ‖i x‖) →
      (sphere c r ⊆ resolventSet ℂ T) →
      (∀ z ∈ sphere c r, ‖resolvent T z‖ ≤ L) →
      (RieszContourIdempotent.projector T c r) ^ 2 = RieszContourIdempotent.projector T c r →
      (∀ n : ℕ, T ^ n * ContourProjectorContinuity.contour
        (fun z => (z ^ n)⁻¹ • resolvent T z) c r = RieszContourIdempotent.projector T c r) →
      ∀ x : E, ‖(RieszContourIdempotent.projector T c r) x‖ ≤
        K * ‖i ((RieszContourIdempotent.projector T c r) x)‖ := by
  have hapos : 0 < a := hα.trans_lt ha
  have tend : Tendsto (fun n : ℕ => (C * r * L) * (α / a) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hα hapos.le)
        ((div_lt_one hapos).mpr ha)).const_mul (C * r * L)
  obtain ⟨n, hn⟩ := (tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists
  let H := D * M ^ n * r * (a ^ n)⁻¹
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  obtain ⟨η, hη, hηsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 4) H
  obtain ⟨B, hB, resolver⟩ := UniformFamilyWeakResolventBound.exists_bound i
    α M C D Cw a outer L hα hM hC hD hCw ha houter hL η hη
  let A := (C * r * L) * (α / a) ^ n
  have gap : 0 < 1 - A - H * η := by dsimp only [A]; linarith
  let K := (H * B) / (1 - A - H * η)
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hH hB) gap.le
  refine ⟨K, hK, fun T strong weak res normR idem moments x => ?_⟩
  let P := RieszContourIdempotent.projector T c r
  let y := P x
  let Q := ContourProjectorContinuity.contour (fun z => (z ^ n)⁻¹ • resolvent T z) c r
  have powerMoment : (T ^ n) (Q y) = y := by
    have hh := congrArg (fun S : E →L[ℂ] E => S y) (moments n)
    change (T ^ n) (Q y) = P (P x) at hh
    have hid : P (P x) = P x := by
      have he := congrArg (fun S : E →L[ℂ] E => S x) idem
      simpa only [pow_two, mul_apply_eq_comp] using he
    exact hh.trans hid
  have normQ : ‖Q y‖ ≤ (r * ((a ^ n)⁻¹ * L)) * ‖y‖ := (Q.le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (ContourMomentNorms.strong_bound T n c r a L hr hapos lower res normR)
      (norm_nonneg y))
  have weakQ : ‖i (Q y)‖ ≤ r * ((a ^ n)⁻¹ * (η * ‖y‖ + B * ‖i y‖)) :=
    ContourMomentNorms.weak_bound T i n c r a η B hr hapos lower res
      (fun z hz => resolver T strong weak z (lower z hz) (upper z hz) (res hz) (normR z hz)) y
  have ly := strong n (Q y)
  rw [powerMoment] at ly
  have estimate : ‖y‖ ≤ A * ‖y‖ + H * η * ‖y‖ + H * B * ‖i y‖ := by
    have hh := ly.trans (add_le_add
      (mul_le_mul_of_nonneg_left normQ (mul_nonneg hC (pow_nonneg hα n)))
      (mul_le_mul_of_nonneg_left weakQ (mul_nonneg hD (pow_nonneg hM n))))
    apply hh.trans_eq
    dsimp only [A, H]
    simp only [div_eq_mul_inv]
    ring
  change ‖y‖ ≤ ((H * B) / (1 - A - H * η)) * ‖i y‖
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ gap).mpr
  nlinarith

end LeanShared.UniformRieszRangeCoercivity
