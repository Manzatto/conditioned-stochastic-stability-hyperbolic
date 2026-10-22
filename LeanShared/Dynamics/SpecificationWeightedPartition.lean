module

public import LeanShared.Dynamics.WeightedSeparatedOrbitGluing
public import LeanShared.Dynamics.OrbitEnergyConcatenation
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Ordinary two-segment point specification and Bowen distortion give
weighted separated-set gluing. Transition energy is bounded by the actual
potential norm; no finite-set or partition multiplication source is used. -/
public noncomputable section
open Set
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 1600000 in
theorem pair_tracing_weighted_gluing (T : X → X) (φ : X →ᵇ ℝ)
    (ε D : ℝ) (positiveε : 0 < ε) (gap : ℕ) (positiveGap : 0 < gap)
    (tracing : ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
      (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < ε) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < ε)
    (bowen : ∀ n x y, (∀ j ≤ n, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ (n + 1) x - orbitSum T φ (n + 1) y| ≤ D) :
    ∀ n m : ℕ, ∀ s t : Finset X,
      Separated T univ (n + 1) (3 * ε) s → Separated T univ (m + 1) (3 * ε) t →
      ∃ q : Finset X, Separated T univ (n + gap + m + 1) ε q ∧
        Real.exp (-(2 * D + (gap - 1 : ℕ) * ‖φ‖)) *
          (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) *
          (∑ y ∈ t, Real.exp (orbitSum T φ (m + 1) y)) ≤
            ∑ z ∈ q, Real.exp (orbitSum T φ (n + gap + m + 1) z) := by
  intro n m s t first second
  choose z firstTrace secondTrace using
    (fun p : {p : X × X // p ∈ s.product t} => tracing n m p.val.1 p.val.2)
  apply weighted_traced_pairs T univ s t n m gap ε positiveε first second
    z (fun _ => mem_univ _) firstTrace secondTrace
    (fun x => Real.exp (orbitSum T φ (n + gap + m + 1) x))
    (fun x => Real.exp (orbitSum T φ (n + 1) x))
    (fun y => Real.exp (orbitSum T φ (m + 1) y))
    (Real.exp (-(2 * D + (gap - 1 : ℕ) * ‖φ‖)))
  intro p
  have firstEnergy := bowen n (z p) p.val.1 (firstTrace p)
  have secondEnergy := bowen m (T^[n + gap] (z p)) p.val.2 (fun j hj => by
    rw [← Function.iterate_add_apply, Nat.add_comm j (n + gap)]
    exact secondTrace p j hj)
  have energy := orbitSum_gluing_lower T φ univ (fun _ _ => mem_univ _) ‖φ‖
    (fun x _ => (abs_le.mp (φ.norm_coe_le_norm x)).1) n m gap positiveGap
    p.val.1 p.val.2 (z p) (mem_univ _) D firstEnergy secondEnergy
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end LeanShared.ThermodynamicDefinitions
