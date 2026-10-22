module
public import LeanShared.Analysis.ConeNeighborWeightBound
public import Mathlib.Analysis.Complex.Norm

/-! Exact physical block normalizations and their neighboring ratio bounds. -/
public noncomputable section
namespace LeanShared.ConeSymbolOverlap
open BTLinkedDyadicWeights

@[expose] def anisotropicWeight (t s:ℝ) (j:ℕ×Bool) : ℂ :=
  ((2:ℝ)^(exponent t s j.2*j.1):ℝ)

theorem anisotropicWeight_nonzero (t s:ℝ) (j:ℕ×Bool) : anisotropicWeight t s j≠0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact (Real.rpow_pos_of_pos (by norm_num) _).ne'

theorem anisotropicWeight_ratio_norm (t s:ℝ) (n l:ℕ) (σ τ:Bool) :
    ‖anisotropicWeight t s (n,σ)/anisotropicWeight t s (l,τ)‖=
      (2:ℝ)^(exponent t s σ*n-exponent t s τ*l) := by
  unfold anisotropicWeight
  rw [norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _),Real.rpow_sub (by norm_num)]
end LeanShared.ConeSymbolOverlap
