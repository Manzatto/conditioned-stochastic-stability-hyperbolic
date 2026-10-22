module
public import LeanShared.Dynamics.FiniteGibbsBowenCylinder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Uniform exponential partition bounds normalize the actual finite Gibbs
cylinder estimates. Prefix and suffix lengths cancel exactly against the
full partition, leaving the prescribed middle energy minus its pressure. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 1600000 in
theorem finite_gibbs_normalized_cylinder
    (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (ε D P A B : ℝ) (positiveε : 0 < ε)
    (positiveA : 0 < A) (nonnegativeB : 0 ≤ B)
    (bowen : ∀ h x y, (∀ j < h, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ h x - orbitSum T φ h y| ≤ D)
    (n k m : ℕ) (z : X) (s : Finset X) (nonempty : s.Nonempty)
    (separated : Separated T univ (n + k + m) (3 * ε) s)
    (first : separatedPartitionSum T φ univ n ε ≤ ENNReal.ofReal (B * Real.exp ((n : ℝ) * P)))
    (last : separatedPartitionSum T φ univ m ε ≤ ENNReal.ofReal (B * Real.exp ((m : ℝ) * P)))
    (total : A * Real.exp (((n + k + m : ℕ) : ℝ) * P) ≤
      ∑ x ∈ s, Real.exp (orbitSum T φ (n + k + m) x))
    (U : Set X) (measurable : MeasurableSet U)
    (inside : ∀ x ∈ U, ∀ j < k, dist (T^[n + j] x) (T^[j] z) < ε) :
    let : Nonempty s := nonempty.to_subtype
    (FiniteAtomicProbability.gibbs (fun x : s => orbitSum T φ (n + k + m) x.val)
      Subtype.val : Measure X) U ≤
      ENNReal.ofReal ((Real.exp (3 * D) * B ^ 2 / A) *
        Real.exp (orbitSum T φ k z - (k : ℝ) * P)) := by
  classical
  let : Nonempty s := nonempty.to_subtype
  dsimp only
  have raw := finite_gibbs_cylinder_bound T c positiveC expansive φ ε D positiveε bowen
    n k m z s nonempty separated U measurable inside
  have top := mul_le_mul' (mul_le_mul'
    (le_refl (ENNReal.ofReal (Real.exp (3 * D + orbitSum T φ k z)))) first) last
  have bottom := ENNReal.ofReal_le_ofReal total
  have normalized := raw.trans (ENNReal.div_le_div top bottom)
  have denominatorPositive : 0 < A * Real.exp (((n + k + m : ℕ) : ℝ) * P) :=
    mul_pos positiveA (Real.exp_pos _)
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg nonnegativeB (Real.exp_nonneg _))),
    ← ENNReal.ofReal_div_of_pos denominatorPositive] at normalized
  have equality : (Real.exp (3 * D + orbitSum T φ k z) *
      (B * Real.exp ((n : ℝ) * P)) * (B * Real.exp ((m : ℝ) * P))) /
        (A * Real.exp (((n + k + m : ℕ) : ℝ) * P)) =
      (Real.exp (3 * D) * B ^ 2 / A) * Real.exp (orbitSum T φ k z - (k : ℝ) * P) := by
    simp only [Nat.cast_add, add_mul, Real.exp_add, Real.exp_sub]
    field_simp
  exact normalized.trans_eq (congrArg ENNReal.ofReal equality)

end LeanShared.ThermodynamicDefinitions
