module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact normalized ratios for the two actual dyadic frequencies. -/
public noncomputable section
namespace LeanShared.DyadicFrequencyScale

@[expose] def major (n l:ℕ):ℝ:=(2:ℝ)^(max n l)
@[expose] def leftRatio (n l:ℕ):ℝ:=(2:ℝ)^n/major n l
@[expose] def rightRatio (n l:ℕ):ℝ:=(2:ℝ)^l/major n l

theorem positive (n l:ℕ):0<major n l:=pow_pos (by norm_num) _
theorem large (n l:ℕ):1≤major n l:=one_le_pow₀ (by norm_num)

theorem left_bound (n l:ℕ):‖leftRatio n l‖≤1:=by
  have hp:=positive n l
  rw [leftRatio,Real.norm_eq_abs,abs_of_nonneg (by positivity),div_le_one (positive n l)]
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_max_left n l)

theorem right_bound (n l:ℕ):‖rightRatio n l‖≤1:=by
  have hp:=positive n l
  rw [rightRatio,Real.norm_eq_abs,abs_of_nonneg (by positivity),div_le_one (positive n l)]
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_max_right n l)

theorem left_identity (n l:ℕ):major n l*leftRatio n l=(2:ℝ)^n:=by
  rw [leftRatio,mul_div_cancel₀ _ (positive n l).ne']

theorem right_identity (n l:ℕ):major n l*rightRatio n l=(2:ℝ)^l:=by
  rw [rightRatio,mul_div_cancel₀ _ (positive n l).ne']

theorem decay (n l:ℕ) (α:ℝ):(major n l^α)⁻¹=(2:ℝ)^(-α*(max n l:ℕ)):=by
  rw [major,←Real.rpow_natCast,←Real.rpow_mul (by norm_num),←Real.rpow_neg (by norm_num)]
  congr 1
  ring
end LeanShared.DyadicFrequencyScale
