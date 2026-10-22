module
public import LeanShared.Analysis.AdaptedWordPrincipalDecay
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-! The actual adapted row decay leaves a strict pressure budget. The
pressure slack and target spectral radius are chosen before all fixed-word
cost prefactors and before the large block length. -/
public noncomputable section
open Filter
open scoped Topology
namespace LeanShared.AdaptedPrincipalPressureBudget

theorem exists_budget {μ ν t s : ℝ} (positiveμ : 0 < μ) (smallμ : μ < 1)
    (largeν : 1 < ν) (positiveT : 0 < t) (negativeS : s < 0)
    (A P : ℝ) (nonnegativeA : 0 ≤ A) :
    ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧ ρ < Real.exp P ∧ ∀ D : ℝ, 0 < D →
      ∀ᶠ N : ℕ in atTop,
        A * max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s) *
          (D * Real.exp ((N : ℝ)*(P+ε))) < ρ^N := by
  obtain ⟨C,γ,positiveC,positiveγ,smallγ,decay⟩ :=
    AdaptedWordPrincipalDecay.exists_decay positiveμ smallμ largeν positiveT negativeS
  let ε := -Real.log γ/4
  let ρ := Real.exp (P+Real.log γ/2)
  have negativeLog : Real.log γ < 0 := Real.log_neg positiveγ smallγ
  have positiveε : 0 < ε := by dsimp [ε]; linarith
  have positiveρ : 0 < ρ := Real.exp_pos _
  have belowPressure : ρ < Real.exp P := Real.exp_lt_exp.mpr (by linarith)
  refine ⟨ε,ρ,positiveε,positiveρ,belowPressure,?_⟩
  intro D positiveD
  let R := γ * Real.exp (P+ε)
  have positiveR : 0 < R := mul_pos positiveγ (Real.exp_pos _)
  have smallR : R < ρ := by
    change γ * Real.exp (P+ε) < Real.exp (P+Real.log γ/2)
    rw [← Real.exp_log positiveγ, ← Real.exp_add]
    simp only [Real.log_exp]
    apply Real.exp_lt_exp.mpr
    dsimp [ε]
    linarith
  have ratioNonnegative : 0 ≤ R/ρ := div_nonneg positiveR.le positiveρ.le
  have ratioSmall : R/ρ < 1 := (div_lt_one positiveρ).mpr smallR
  have tends : Tendsto (fun N : ℕ => (A*C*D)*(R/ρ)^N) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioSmall)
  filter_upwards [tends.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with N small
  have strict : (A*C*D)*R^N < ρ^N := by
    apply (div_lt_one (pow_pos positiveρ N)).mp
    simpa only [div_pow, mul_div_assoc] using small
  calc
    _ ≤ (A*(C*γ^N))*(D*Real.exp ((N:ℝ)*(P+ε))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (decay N) nonnegativeA)
        (mul_nonneg positiveD.le (Real.exp_pos _).le)
    _ = (A*C*D)*R^N := by
      rw [Real.exp_nat_mul, mul_pow]
      ring
    _ < _ := strict

end LeanShared.AdaptedPrincipalPressureBudget
