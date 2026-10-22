module
public import LeanShared.Analysis.BTLinkedDyadicWeights
public import LeanShared.Analysis.DyadicFrequencyScale

/-! The literal floor/log thresholds leave the strict radial margin
needed by the actual same-sign nonstationary kernel. -/
public noncomputable section
namespace LeanShared.BTNonlinkedRadialRatios
open BTLinkedDyadicWeights DyadicFrequencyScale

theorem upper_scale {L:ℝ} (positive:0<L) (n l:ℕ)
    (nonlinked:(l:ℤ)+plusThreshold L<(n:ℤ)):
    16*L*(2:ℝ)^l≤(2:ℝ)^n:=by
  have floor:=Int.lt_floor_add_one (Real.logb 2 L)
  have level:(l:ℝ)+(plusThreshold L:ℝ)<(n:ℝ):=by exact_mod_cast nonlinked
  have threshold:(plusThreshold L:ℝ)=(⌊Real.logb 2 L⌋:ℤ)+6:=by
    simp only [plusThreshold,Int.cast_add,Int.cast_ofNat]
  have exponents:Real.logb 2 L+4+(l:ℝ)≤n:=by rw [threshold] at level;linarith
  have bound:=Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) exponents
  rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) positive] at bound
  norm_num only [Real.rpow_natCast,Nat.cast_ofNat,pow_succ,pow_zero,mul_one] at bound
  nlinarith

theorem lower_scale {L:ℝ} (positive:0<L) (n l:ℕ)
    (nonlinked:(n:ℤ)<(l:ℤ)+minusThreshold L):
    16*L⁻¹*(2:ℝ)^n≤(2:ℝ)^l:=by
  have floor:=Int.floor_le (Real.logb 2 L)
  have level:(n:ℝ)<(l:ℝ)+(minusThreshold L:ℝ):=by exact_mod_cast nonlinked
  have threshold:(minusThreshold L:ℝ)=(⌊Real.logb 2 L⌋:ℤ)-6:=by
    simp only [minusThreshold,Int.cast_sub,Int.cast_ofNat]
  have exponents:(n:ℝ)+4≤Real.logb 2 L+(l:ℝ):=by rw [threshold] at level;linarith
  have bound:=Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) exponents
  rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) positive] at bound
  norm_num only [Real.rpow_natCast,Nat.cast_ofNat,pow_succ,pow_zero,mul_one] at bound
  apply (mul_le_mul_iff_right₀ positive).mp
  calc
    L*(16*L⁻¹*(2:ℝ)^n)=16*(2:ℝ)^n:=by field_simp
    _≤L*((2:ℝ)^l):=by nlinarith

theorem upper_ratio {L:ℝ} (positive:0<L) (n l:ℕ)
    (nonlinked:(l:ℤ)+plusThreshold L<(n:ℤ)):
    16*L*rightRatio n l≤leftRatio n l:=by
  dsimp only [rightRatio,leftRatio]
  rw [←mul_div_assoc]
  exact div_le_div_of_nonneg_right (upper_scale positive n l nonlinked) (DyadicFrequencyScale.positive n l).le

theorem lower_ratio {L:ℝ} (positive:0<L) (n l:ℕ)
    (nonlinked:(n:ℤ)<(l:ℤ)+minusThreshold L):
    16*L⁻¹*leftRatio n l≤rightRatio n l:=by
  dsimp only [rightRatio,leftRatio]
  rw [←mul_div_assoc]
  exact div_le_div_of_nonneg_right (lower_scale positive n l nonlinked) (DyadicFrequencyScale.positive n l).le
end LeanShared.BTNonlinkedRadialRatios
