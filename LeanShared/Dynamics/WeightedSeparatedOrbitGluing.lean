module

public import LeanShared.Dynamics.SeparatedOrbitGluing
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Weighted separated-orbit gluing preserves the product partition sum.
The actual chosen shadowing points are used throughout, so no unrelated
existential finite set replaces their energies. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 1600000 in
theorem weighted_traced_pairs (T : X → X) (K : Set X)
    (s t : Finset X) (n m gap : ℕ) (ε : ℝ) (positive : 0 < ε)
    (first : Separated T K (n + 1) (3 * ε) s)
    (second : Separated T K (m + 1) (3 * ε) t)
    (trace : {p : X × X // p ∈ s.product t} → X)
    (member : ∀ p, trace p ∈ K)
    (traceFirst : ∀ p, ∀ j ≤ n, dist (T^[j] (trace p)) (T^[j] p.val.1) < ε)
    (traceSecond : ∀ p, ∀ j ≤ m,
      dist (T^[n + gap + j] (trace p)) (T^[j] p.val.2) < ε)
    (weight u v : X → ℝ) (a : ℝ)
    (weightBound : ∀ p, a * u p.val.1 * v p.val.2 ≤ weight (trace p)) :
    ∃ q : Finset X, Separated T K (n + gap + m + 1) ε q ∧
      a * (∑ x ∈ s, u x) * (∑ y ∈ t, v y) ≤ ∑ z ∈ q, weight z := by
  classical
  have separates := traced_pair_separation T K s t n m gap ε first second trace traceFirst traceSecond
  have injective : Function.Injective trace := by
    intro p q equal
    by_contra different
    obtain ⟨j, _, apart⟩ := separates p q different
    rw [equal, dist_self] at apart
    exact (not_le_of_gt positive) apart
  refine ⟨Finset.univ.image trace, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact member p
  · intro x hx y hy different
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
    exact separates p q (fun equal => different (congrArg trace equal))
  · have productSum : (∑ p : {p : X × X // p ∈ s.product t}, a * u p.val.1 * v p.val.2) =
        a * (∑ x ∈ s, u x) * (∑ y ∈ t, v y) := by
      calc
        _ = ∑ p ∈ s.product t, a * u p.1 * v p.2 :=
          Finset.sum_coe_sort (s.product t) (fun p : X × X => a * u p.1 * v p.2)
        _ = ∑ x ∈ s, ∑ y ∈ t, a * u x * v y := by
          rw [Finset.product_eq_sprod, Finset.sum_product]
        _ = _ := by
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [← productSum, Finset.sum_image (fun _ _ _ _ equal => injective equal)]
    exact Finset.sum_le_sum (fun p _ => weightBound p)

end LeanShared.ThermodynamicDefinitions
