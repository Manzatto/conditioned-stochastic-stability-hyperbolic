module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Ring.Pow

/-! Balancing a freely chosen geometric window against its exponential
rank cost produces a genuine geometric bound in the period. -/

public section
namespace LeanShared.GeometricWindowBalance

theorem bound (θ τ b A B : ℝ) (positiveθ : 0 < θ) (smallθ : θ < 1)
    (nonnegativeτ : 0 ≤ τ) (smallτ : τ < 1) (nonnegativeb : 0 ≤ b)
    (nonnegativeA : 0 ≤ A) (nonnegativeB : 0 ≤ B) :
    ∃ κ C : ℝ, 0 < κ ∧ κ < 1 ∧ 0 ≤ C ∧ ∀ n : ℕ, ∃ m : ℕ,
      A * θ ^ m + B * b ^ m * τ ^ n ≤ C * κ ^ n := by
  obtain ⟨k, smallPower⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (b + 1) by positivity) smallτ
  let L := k + 1
  have positiveL : 0 < L := by dsimp [L]; omega
  have positiveDenom : 0 < (L : ℝ) + 1 := by positivity
  have cost : b * τ ^ L < 1 := by
    have raw : (b + 1) * τ ^ k < 1 := by
      have := (lt_div_iff₀ (show 0 < b + 1 by positivity)).mp smallPower
      nlinarith
    apply lt_of_le_of_lt _ raw
    calc
      b * τ ^ L ≤ b * τ ^ k := by
        apply mul_le_mul_of_nonneg_left _ nonnegativeb
        exact pow_le_pow_of_le_one nonnegativeτ smallτ.le (by dsimp [L]; omega)
      _ ≤ (b + 1) * τ ^ k := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg nonnegativeτ _)
  let η := max θ (b * τ ^ L)
  have positiveη : 0 < η := positiveθ.trans_le (le_max_left _ _)
  have smallη : η < 1 := max_lt smallθ cost
  let κ := 1 - (1 - η) / ((L : ℝ) + 1)
  have positiveκ : 0 < κ := by
    have fraction : (1 - η) / ((L : ℝ) + 1) < 1 := by
      apply (div_lt_one positiveDenom).mpr
      have : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
      linarith
    dsimp [κ]
    linarith
  have smallκ : κ < 1 := by
    have fraction : 0 < (1 - η) / ((L : ℝ) + 1) := div_pos (by linarith) positiveDenom
    dsimp [κ]
    linarith
  have slowPower : η ≤ κ ^ L := by
    have bernoulli := one_add_mul_sub_le_pow (show -1 ≤ κ by linarith) L
    have algebra : 1 + (L : ℝ) * (κ - 1) - η = (1 - η) / ((L : ℝ) + 1) := by
      dsimp [κ]
      field_simp
      ring
    have fraction : 0 ≤ (1 - η) / ((L : ℝ) + 1) := by positivity
    linarith
  refine ⟨κ, (A + B) / κ ^ L, positiveκ, smallκ, by positivity, ?_⟩
  intro n
  let m := n / L
  let j := n % L
  have decomposition : n = L * m + j := (Nat.div_add_mod n L).symm
  have remainder : j < L := Nat.mod_lt n positiveL
  have θbound : θ ^ m ≤ κ ^ (L * m) := by
    calc
      _ ≤ η ^ m := pow_le_pow_left₀ positiveθ.le (le_max_left _ _) _
      _ ≤ (κ ^ L) ^ m := pow_le_pow_left₀ positiveη.le slowPower _
      _ = _ := by rw [pow_mul]
  have costbound : b ^ m * τ ^ n ≤ κ ^ (L * m) := by
    rw [decomposition, pow_add, pow_mul, ← mul_assoc, ← mul_pow]
    calc
      _ ≤ (b * τ ^ L) ^ m := mul_le_of_le_one_right (by positivity)
        (pow_le_one₀ nonnegativeτ smallτ.le)
      _ ≤ η ^ m := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
      _ ≤ (κ ^ L) ^ m := pow_le_pow_left₀ positiveη.le slowPower _
      _ = _ := by rw [pow_mul]
  have slowRemainder : κ ^ L ≤ κ ^ j :=
    pow_le_pow_of_le_one positiveκ.le smallκ.le remainder.le
  have finalCost : κ ^ (L * m) ≤ κ ^ n / κ ^ L := by
    apply (le_div_iff₀ (pow_pos positiveκ _)).mpr
    conv_rhs => rw [decomposition, pow_add]
    exact mul_le_mul_of_nonneg_left slowRemainder (pow_nonneg positiveκ.le _)
  refine ⟨m, ?_⟩
  calc
    _ ≤ (A + B) * κ ^ (L * m) := by
      have h₁ := mul_le_mul_of_nonneg_left θbound nonnegativeA
      have h₂ := mul_le_mul_of_nonneg_left costbound nonnegativeB
      nlinarith
    _ ≤ (A + B) * (κ ^ n / κ ^ L) :=
      mul_le_mul_of_nonneg_left finalCost (add_nonneg nonnegativeA nonnegativeB)
    _ = _ := by ring

end LeanShared.GeometricWindowBalance
