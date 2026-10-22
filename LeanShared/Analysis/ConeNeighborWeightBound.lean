module
public import LeanShared.Analysis.ConeNeighborResolution
public import LeanShared.Analysis.BTLinkedDyadicWeights

/-! The neighboring cone resolution has a uniform anisotropic weight cost
once the forbidden high-frequency sign interaction is excluded. -/
public section
namespace LeanShared.ConeSymbolOverlap
open BTLinkedDyadicWeights

theorem neighbor_exponent_bound (t s : ℝ) (order : s≤t)
    (n l:ℕ) (σ τ:Bool) (close : n≤l+1 ∧ l≤n+1)
    (allowed : σ=true→τ=false→n≤1) :
    exponent t s σ*n-exponent t s τ*l≤3*(|s|+|t|) := by
  have nnonnegative : (0:ℝ)≤n := Nat.cast_nonneg _
  have lnonnegative : (0:ℝ)≤l := Nat.cast_nonneg _
  have left : (n:ℝ)≤(l:ℝ)+1 := by exact_mod_cast close.1
  have right : (l:ℝ)≤(n:ℝ)+1 := by exact_mod_cast close.2
  have difference : |(n:ℝ)-(l:ℝ)|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have same (e:ℝ) : e*n-e*l≤|e| := by
    calc
      _ = e*((n:ℝ)-(l:ℝ)) := by ring
      _ ≤ |e*((n:ℝ)-(l:ℝ))| := le_abs_self _
      _ = |e| * |(n:ℝ)-(l:ℝ)| := abs_mul _ _
      _ ≤ |e| *1 := mul_le_mul_of_nonneg_left difference (abs_nonneg e)
      _ = _ := mul_one _
  cases σ <;> cases τ
  · change s*n-s*l≤_
    nlinarith [same s,abs_nonneg s,abs_nonneg t]
  · change s*n-t*l≤_
    nlinarith [same s,mul_nonneg (sub_nonneg.mpr order) lnonnegative,abs_nonneg s,abs_nonneg t]
  · change t*n-s*l≤_
    have nsmall : (n:ℝ)≤1 := by exact_mod_cast allowed rfl rfl
    have lsmall : (l:ℝ)≤2 := by linarith
    have tn : t*n≤|t| := by
      have h:=mul_le_mul_of_nonneg_right (le_abs_self t) nnonnegative
      nlinarith [mul_le_mul_of_nonneg_left nsmall (abs_nonneg t)]
    have sl : -s*l≤2* |s| := by
      have h:=mul_le_mul_of_nonneg_right (neg_le_abs s) lnonnegative
      nlinarith [mul_le_mul_of_nonneg_left lsmall (abs_nonneg s)]
    nlinarith [abs_nonneg s,abs_nonneg t]
  · change t*n-t*l≤_
    nlinarith [same t,abs_nonneg s,abs_nonneg t]

theorem neighbor_weight_bound (t s : ℝ) (order : s≤t)
    (n l:ℕ) (σ τ:Bool) (close : n≤l+1 ∧ l≤n+1)
    (allowed : σ=true→τ=false→n≤1) :
    (2:ℝ)^(exponent t s σ*n-exponent t s τ*l)≤(2:ℝ)^(3*(|s|+|t|)) :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (neighbor_exponent_bound t s order n l σ τ close allowed)

theorem neighbors_card_le (n:ℕ) : (neighbors n).card≤6 := by
  classical
  simp only [neighbors,Finset.card_product,Nat.card_Icc,Finset.card_univ,Fintype.card_bool]
  omega
end LeanShared.ConeSymbolOverlap
