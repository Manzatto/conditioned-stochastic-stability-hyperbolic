module
public import LeanShared.Analysis.BTPrincipalDyadicRows
public import LeanShared.Analysis.BTFiniteFrequencyRemainder

/-! The full physical row split: linked blocks contribute to the strong
coefficient; sharp nonlinked decay and the finite exceptional square
contribute to the weakened norm. Constants are uniform in output frequency. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.BTPhysicalTwoNormRows
open BTLinkedDyadicWeights

theorem bound (t s loss α upper lower P W strong weak : ℝ)
    (ht : 0 < t) (hs : s < 0) (hLoss : 0 ≤ loss) (gap : t-s+loss < α)
    (hu : 0 < upper) (hl : 0 < lower) (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hstrong : 0 ≤ strong) (hweak : 0 ≤ weak)
    (N n : ℕ) (σ : Bool) (J : Finset ℕ) (a : ℕ → Bool → ℝ)
    (linkedBound : ∀ l τ, linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      a l τ ≤ P*(2:ℝ)^(exponent t s σ*n-exponent t s τ*l)*strong)
    (sharpBound : ∀ l τ, ¬ linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      N ≤ max n l → a l τ ≤ W*(2:ℝ)^(
        exponent t s σ*n-(exponent t s τ-loss)*l-α*(max n l:ℕ))*weak)
    (lowBound : ∀ l τ, ¬ linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) →
      max n l < N → a l τ ≤ P*(2:ℝ)^(
        exponent t s σ*n-(exponent t s τ-loss)*l)*weak) :
    (∑ l ∈ J,∑ τ : Bool,a l τ) ≤
      P*((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*
        max (upper^t) (lower^s))*strong +
      (W*(2*(1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹)+
        P*(2*((N:ℝ)*(2:ℝ)^((t-s+loss)*N))))*weak := by
  let principal (l : ℕ) (τ : Bool) : ℝ :=
    if linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ) then
      (2:ℝ)^(exponent t s σ*n-exponent t s τ*l) else 0
  let decay (l : ℕ) (τ : Bool) : ℝ := (2:ℝ)^(
    exponent t s σ*n-(exponent t s τ-loss)*l-α*(max n l:ℕ))
  let small (l : ℕ) (τ : Bool) : ℝ := if max n l < N then
    (2:ℝ)^(exponent t s σ*n-(exponent t s τ-loss)*l) else 0
  have principalBound : (∑ l ∈ J,∑ τ : Bool,principal l τ) ≤
      (max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*
        max (upper^t) (lower^s) := by
    have h := principal_row_bound t s upper lower ht hs hu hl (n,σ) J
    simpa only [principal,Fintype.sum_bool,Finset.sum_add_distrib,Finset.sum_filter,exponent] using h
  have decayBound : (∑ l ∈ J,∑ τ : Bool,decay l τ) ≤
      2*(1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹ := by
    have h := BTWeakDyadicRows.row_bound t s loss α ht.le hs.le hLoss gap n σ J J
    simpa only [decay,Fintype.sum_bool,Finset.sum_add_distrib,exponent] using h
  have smallBound := BTFiniteFrequencyRemainder.row_bound t s loss ht.le hs.le hLoss N n σ J
  have point (l : ℕ) (τ : Bool) : a l τ ≤
      P*principal l τ*strong+W*decay l τ*weak+P*small l τ*weak := by
    have dp : 0 ≤ W*decay l τ*weak := by dsimp [decay]; positivity
    have sp : 0 ≤ P*small l τ*weak := by dsimp [small]; split_ifs <;> positivity
    have pp : 0 ≤ P*principal l τ*strong := by dsimp [principal]; split_ifs <;> positivity
    by_cases h : linked (plusThreshold upper) (minusThreshold lower) (n,σ) (l,τ)
    · have hbound := linkedBound l τ h
      simp only [principal,ite_eq_left h] at *
      linarith
    · by_cases high : N ≤ max n l
      · have hbound := sharpBound l τ h high
        change a l τ ≤ W*decay l τ*weak at hbound
        linarith
      · have lo : max n l < N := Nat.lt_of_not_ge high
        have hbound := lowBound l τ h lo
        simp only [small,ite_eq_left lo] at *
        linarith
  calc
    _ ≤ ∑ l ∈ J,∑ τ : Bool,
        (P*principal l τ*strong+W*decay l τ*weak+P*small l τ*weak) :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun τ _ => point l τ))
    _ = P*(∑ l ∈ J,∑ τ : Bool,principal l τ)*strong+
        W*(∑ l ∈ J,∑ τ : Bool,decay l τ)*weak+
        P*(∑ l ∈ J,∑ τ : Bool,small l τ)*weak := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := by
      have a := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left principalBound hP) hstrong
      have b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left decayBound hW) hweak
      have c := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left smallBound hP) hweak
      dsimp only [small] at c ⊢
      nlinarith

end LeanShared.BTPhysicalTwoNormRows
