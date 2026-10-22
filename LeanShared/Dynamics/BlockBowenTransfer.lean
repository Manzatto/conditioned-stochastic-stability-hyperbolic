module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

/-! A uniform block-orbit Bowen estimate gives the usual one-step Bowen
estimate by splitting the energy into residue classes and a bounded tail. -/
public section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem sum_range_blocks (f : ℕ → ℝ) (N q : ℕ) :
    (∑ j ∈ Finset.range (N * q), f j) =
      ∑ r ∈ Finset.range N, ∑ j ∈ Finset.range q, f (N * j + r) := by
  induction q with
  | zero => simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero]
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]

set_option maxHeartbeats 1600000 in
theorem one_step_bowen_of_blocks (T : X → X) (K : Set X) (invariant : MapsTo T K K)
    (φ : X → ℝ) (B D η : ℝ) (Bnonnegative : 0 ≤ B)
    (bounded : ∀ x ∈ K, |φ x| ≤ B)
    (N : ℕ) (positiveN : 0 < N)
    (block : ∀ q : ℕ, ∀ x ∈ K, ∀ y ∈ K,
      (∀ j < q, dist (T^[N * j] x) (T^[N * j] y) < η) →
      |(∑ j ∈ Finset.range q, φ (T^[N * j] x)) -
        (∑ j ∈ Finset.range q, φ (T^[N * j] y))| ≤ D) :
    ∀ n : ℕ, ∀ x ∈ K, ∀ y ∈ K,
      (∀ j < n, dist (T^[j] x) (T^[j] y) < η) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ (N : ℝ) * D + 2 * N * B := by
  intro n x hx y hy close
  let q := n / N
  let r := n % N
  have size : N * q + r = n := by
    dsimp [q, r]
    exact Nat.div_add_mod n N
  have remainderSmall : r < N := Nat.mod_lt _ positiveN
  let h := fun j : ℕ => φ (T^[j] x) - φ (T^[j] y)
  have residue (i : ℕ) (hi : i < N) :
      |∑ j ∈ Finset.range q, h (N * j + i)| ≤ D := by
    have estimate := block q (T^[i] x) (invariant.iterate i hx)
      (T^[i] y) (invariant.iterate i hy) (fun j hj => by
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]
        apply close
        have strict : N * j + i < N * q := by nlinarith
        exact strict.trans_le (by omega))
    simpa only [← Finset.sum_sub_distrib, ← Function.iterate_add_apply, h] using estimate
  have tail (j : ℕ) : |h j| ≤ 2 * B := by
    exact (abs_sub (φ (T^[j] x)) (φ (T^[j] y))).trans
      ((add_le_add (bounded _ (invariant.iterate j hx))
        (bounded _ (invariant.iterate j hy))).trans_eq (by ring))
  have energies : orbitSum T φ n x - orbitSum T φ n y = ∑ j ∈ Finset.range n, h j := by
    simp only [orbitSum, Finset.sum_sub_distrib, h]
  rw [energies, ← size, Finset.sum_range_add, sum_range_blocks]
  calc
    _ ≤ |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range q, h (N * j + i)| +
        |∑ j ∈ Finset.range r, h (N * q + j)| := abs_add_le _ _
    _ ≤ (∑ i ∈ Finset.range N, |∑ j ∈ Finset.range q, h (N * j + i)|) +
        ∑ j ∈ Finset.range r, |h (N * q + j)| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ _i ∈ Finset.range N, D) + ∑ _j ∈ Finset.range r, 2 * B :=
      add_le_add (Finset.sum_le_sum (fun i hi => residue i (Finset.mem_range.mp hi)))
        (Finset.sum_le_sum (fun j _ => tail _))
    _ = (N : ℝ) * D + (r : ℝ) * (2 * B) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (N : ℝ) * D + 2 * N * B := by
      have cast : (r : ℝ) ≤ N := by exact_mod_cast remainderSmall.le
      nlinarith

end LeanShared.ThermodynamicDefinitions
