module
public import LeanShared.Analysis.ProjectionConeTransversality
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Closed smaller projection cones lie strictly inside larger cones away
from zero. A strict radial gap produces their actual cone action, and
contracting/expanding word rates provide that gap for every large length. -/
public noncomputable section
open Set Filter
namespace LeanShared.ProjectionConeRadialMargin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closed (P : E →L[ℝ] E) (a : ℝ) : IsClosed (ProjectionConeTransversality.cone P a) :=
  isClosed_le P.continuous.norm ((continuous_id.sub P.continuous).norm.const_mul a)

theorem nonzero_mem_interior (P : E →L[ℝ] E) {a b : ℝ} (less : a < b)
    {v : E} (member : v ∈ ProjectionConeTransversality.cone P a) (nonzero : v ≠ 0) :
    v ∈ interior (ProjectionConeTransversality.cone P b) := by
  have residual : 0 < ‖v-P v‖ := by
    apply norm_pos_iff.mpr
    intro zero
    have equal : v=P v := sub_eq_zero.mp zero
    have zeroP : P v=0 := norm_eq_zero.mp (le_antisymm (by
      change ‖P v‖ ≤ a*‖v-P v‖ at member
      simpa only [zero,norm_zero,mul_zero] using member) (norm_nonneg _))
    exact nonzero (equal.trans zeroP)
  have strict : ‖P v‖ < b*‖v-P v‖ :=
    member.trans_lt (mul_lt_mul_of_pos_right less residual)
  have openStrict : IsOpen {w : E | ‖P w‖ < b*‖w-P w‖} :=
    isOpen_lt P.continuous.norm ((continuous_id.sub P.continuous).norm.const_mul b)
  have inside : {w : E | ‖P w‖ < b*‖w-P w‖} ⊆ ProjectionConeTransversality.cone P b := by
    intro w hw
    change ‖P w‖ ≤ b*‖w-P w‖
    exact hw.le
  exact interior_mono inside (openStrict.interior_eq.symm ▸ strict)

theorem smul_mem (P : E →L[ℝ] E) {a c : ℝ} (nonnegative : 0 ≤ c)
    {v : E} (member : v ∈ ProjectionConeTransversality.cone P a) :
    c • v ∈ ProjectionConeTransversality.cone P a := by
  change ‖P (c • v)‖ ≤ a*‖c • v-P (c • v)‖
  rw [map_smul,←smul_sub,norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg nonnegative]
  exact (mul_le_mul_of_nonneg_left member nonnegative).trans_eq (by ring)

theorem cone_action_of_radial_gap (A : E →L[ℝ] E) {source target : Set E}
    {upper lower : ℝ} (gap : upper < lower)
    (upperBound : ∀ v, A v ∉ target → ‖A v‖ ≤ upper*‖v‖)
    (lowerBound : ∀ v, v ∉ interior source → lower*‖v‖ ≤ ‖A v‖)
    {v : E} (nonzero : v ≠ 0) (outside : v ∉ interior source) : A v ∈ target := by
  by_contra notMember
  have upperEstimate := upperBound v notMember
  have lowerEstimate := lowerBound v outside
  have strict := mul_lt_mul_of_pos_right gap (norm_pos_iff.mpr nonzero)
  exact (not_lt_of_ge (lowerEstimate.trans upperEstimate)) strict

theorem eventually_radial_gap {μ ν : ℝ} (positiveμ : 0 < μ) (contractingμ : μ < 1)
    (expandingν : 1 < ν) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 10*μ^n < (4*(ν⁻¹)^n)⁻¹ := by
  have positiveν : 0 < ν := lt_trans zero_lt_one expandingν
  have nonnegativeRatio : 0 ≤ μ*ν⁻¹ := by positivity
  have ratioSmall : μ*ν⁻¹ < 1 := by
    have invSmall : ν⁻¹ < 1 := (inv_lt_one₀ positiveν).mpr expandingν
    exact (mul_lt_mul_of_pos_left invSmall positiveμ).trans (by simpa only [mul_one] using contractingμ)
  have convergence := tendsto_pow_atTop_nhds_zero_of_lt_one nonnegativeRatio ratioSmall
  have small : ∀ᶠ n : ℕ in atTop, (μ*ν⁻¹)^n < (1/40:ℝ) :=
    convergence.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/40))
  obtain ⟨N,bound⟩ := eventually_atTop.mp small
  refine ⟨N,fun n large => ?_⟩
  rw [inv_eq_one_div]
  apply (lt_div_iff₀ (by positivity : 0 < 4*(ν⁻¹)^n)).mpr
  calc
    (10*μ^n)*(4*(ν⁻¹)^n) = 40*(μ*ν⁻¹)^n := by rw [mul_pow];ring
    _ < 40*(1/40:ℝ) := mul_lt_mul_of_pos_left (bound n large) (by norm_num)
    _ = 1 := by norm_num

end LeanShared.ProjectionConeRadialMargin
