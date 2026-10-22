module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! A geometric estimate on a padded arithmetic progression extends to
every length when appending finitely many terms has a uniform cost. The
rate is only assumed positive; rates smaller than one are permitted. -/
public noncomputable section
namespace LeanShared.PaddedGeometricGrowth
open scoped BigOperators

theorem exists_all_length_bound (F : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ F n)
    (R G : ℝ) (positiveR : 0 < R) (nonnegativeG : 0 ≤ G)
    (append : ∀ m j, F (m + j) ≤ G ^ j * F m)
    (N h p₀ : ℕ) (positiveN : 0 < N) (A : ℝ) (nonnegativeA : 0 ≤ A)
    (padded : ∀ p, p₀ ≤ p → F (N * p + h) ≤ A * R ^ (N * p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, F n ≤ C * R ^ n := by
  classical
  let cutoff := N * p₀ + h
  let initial := ∑ n ∈ Finset.range cutoff, F n / R ^ n
  let residues := ∑ j ∈ Finset.range N, (G / R) ^ j
  have initialNonnegative : 0 ≤ initial :=
    Finset.sum_nonneg (fun n _ => div_nonneg (nonnegative n) (pow_nonneg positiveR.le n))
  have residuesNonnegative : 0 ≤ residues :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (div_nonneg nonnegativeG positiveR.le) j)
  let C := initial + (A / R ^ h) * residues
  have Cnonnegative : 0 ≤ C := add_nonneg initialNonnegative
    (mul_nonneg (div_nonneg nonnegativeA (pow_nonneg positiveR.le h)) residuesNonnegative)
  refine ⟨C, Cnonnegative, fun n => ?_⟩
  by_cases small : n < cutoff
  · have term : F n / R ^ n ≤ initial :=
      Finset.single_le_sum
        (fun j _ => div_nonneg (nonnegative j) (pow_nonneg positiveR.le j))
        (Finset.mem_range.mpr small)
    have belowC : initial ≤ C := le_add_of_nonneg_right
      (mul_nonneg (div_nonneg nonnegativeA (pow_nonneg positiveR.le h)) residuesNonnegative)
    exact (div_le_iff₀ (pow_pos positiveR n)).mp (term.trans belowC)
  · have large : cutoff ≤ n := Nat.le_of_not_gt small
    have hle : h ≤ n := by dsimp only [cutoff] at large; omega
    let p := (n - h) / N
    let j := (n - h) % N
    have smallJ : j < N := Nat.mod_lt _ positiveN
    have largeP : p₀ ≤ p := by
      apply (Nat.le_div_iff_mul_le positiveN).mpr
      rw [Nat.mul_comm p₀ N]
      dsimp only [cutoff] at large
      omega
    have length : n = (N * p + h) + j := by
      have division := Nat.mod_add_div (n - h) N
      dsimp only [p, j]
      omega
    have residueBound : (G / R) ^ j ≤ residues :=
      Finset.single_le_sum (fun k _ => pow_nonneg (div_nonneg nonnegativeG positiveR.le) k)
        (Finset.mem_range.mpr smallJ)
    have coefficientBound : (A / R ^ h) * (G / R) ^ j ≤ C := by
      have bound := mul_le_mul_of_nonneg_left residueBound
        (div_nonneg nonnegativeA (pow_nonneg positiveR.le h))
      exact bound.trans (le_add_of_nonneg_left initialNonnegative)
    calc
      F n = F ((N * p + h) + j) := congrArg F length
      _ ≤ G ^ j * F (N * p + h) := append _ _
      _ ≤ G ^ j * (A * R ^ (N * p)) :=
        mul_le_mul_of_nonneg_left (padded p largeP) (pow_nonneg nonnegativeG j)
      _ = ((A / R ^ h) * (G / R) ^ j) * R ^ n := by
        rw [length, pow_add, pow_add, div_pow]
        field_simp
      _ ≤ C * R ^ n := mul_le_mul_of_nonneg_right coefficientBound (pow_nonneg positiveR.le n)

end LeanShared.PaddedGeometricGrowth
