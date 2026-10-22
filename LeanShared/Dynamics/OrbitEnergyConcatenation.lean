module

public import LeanShared.Dynamics.ThermodynamicDefinitions
import Mathlib.Tactic.Linarith

/-! Actual orbit energies split at their literal concatenation times.
A transition word loses at most its length times the potential bound. -/
public section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*}

theorem orbitSum_add (T : X → X) (φ : X → ℝ) (n m : ℕ) (x : X) :
    orbitSum T φ (n + m) x = orbitSum T φ n x + orbitSum T φ m (T^[n] x) := by
  unfold orbitSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.add_comm n j, Function.iterate_add_apply]

theorem orbitSum_lower (T : X → X) (φ : X → ℝ) (K : Set X)
    (invariant : MapsTo T K K) (B : ℝ) (lower : ∀ x ∈ K, -B ≤ φ x)
    (n : ℕ) {x : X} (hx : x ∈ K) : -(n : ℝ) * B ≤ orbitSum T φ n x := by
  have bounds := Finset.sum_le_sum (s := Finset.range n)
    (fun j _ => lower (T^[j] x) (invariant.iterate j hx))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg, neg_mul, orbitSum] using bounds

theorem orbitSum_gluing_lower (T : X → X) (φ : X → ℝ) (K : Set X)
    (invariant : MapsTo T K K) (B : ℝ) (lower : ∀ x ∈ K, -B ≤ φ x)
    (n m gap : ℕ) (positiveGap : 0 < gap) (x y z : X) (hz : z ∈ K)
    (D : ℝ)
    (first : |orbitSum T φ (n + 1) z - orbitSum T φ (n + 1) x| ≤ D)
    (second : |orbitSum T φ (m + 1) (T^[n + gap] z) - orbitSum T φ (m + 1) y| ≤ D) :
    orbitSum T φ (n + 1) x + orbitSum T φ (m + 1) y - 2 * D - (gap - 1 : ℕ) * B ≤
      orbitSum T φ (n + gap + m + 1) z := by
  have size : n + gap + m + 1 = (n + 1) + ((gap - 1) + (m + 1)) := by omega
  rw [size, orbitSum_add T φ (n + 1) ((gap - 1) + (m + 1)) z,
    orbitSum_add T φ (gap - 1) (m + 1) (T^[n + 1] z)]
  have time : T^[gap - 1] (T^[n + 1] z) = T^[n + gap] z := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [time]
  have transition := orbitSum_lower T φ K invariant B lower (gap - 1)
    (invariant.iterate (n + 1) hz)
  have firstBound := (abs_le.mp first).1
  have secondBound := (abs_le.mp second).1
  linarith

end LeanShared.ThermodynamicDefinitions
