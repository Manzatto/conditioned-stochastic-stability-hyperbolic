module

public import LeanShared.Dynamics.OrbitEnergyConcatenation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Prod

/-! Splitting a separated orbit into two Bowen-covered pieces is injective
in the pair of cover centers. Actual Bowen energy bounds then give a product
upper bound, with no assumed partition submultiplicativity. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 2000000 in
theorem weighted_orbit_splitting (T : X → X) (φ : X → ℝ)
    (ε D : ℝ) (positiveε : 0 < ε) (n m : ℕ) (s t u : Finset X)
    (separated : Separated T univ (n + m) (3 * ε) s)
    (a b : X → X) (memberA : ∀ x ∈ s, a x ∈ t) (memberB : ∀ x ∈ s, b x ∈ u)
    (firstTrace : ∀ x ∈ s, ∀ j < n, dist (T^[j] x) (T^[j] (a x)) < ε)
    (secondTrace : ∀ x ∈ s, ∀ j < m, dist (T^[n + j] x) (T^[j] (b x)) < ε)
    (bowen : ∀ k x y, (∀ j < k, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ k x - orbitSum T φ k y| ≤ D) :
    (∑ x ∈ s, Real.exp (orbitSum T φ (n + m) x)) ≤
      Real.exp (2 * D) * (∑ y ∈ t, Real.exp (orbitSum T φ n y)) *
        (∑ z ∈ u, Real.exp (orbitSum T φ m z)) := by
  classical
  let e := fun x => (a x, b x)
  have injective : Set.InjOn e s := by
    intro x hx y hy equal
    by_contra different
    obtain ⟨j, hj, apart⟩ := separated.2 x hx y hy different
    have sameA : a x = a y := congrArg Prod.fst equal
    have sameB : b x = b y := congrArg Prod.snd equal
    by_cases first : j < n
    · have nx := firstTrace x hx j first
      have ny := firstTrace y hy j first
      rw [← sameA] at ny
      have triangle := dist_triangle (T^[j] x) (T^[j] (a x)) (T^[j] y)
      rw [dist_comm (T^[j] (a x)) (T^[j] y)] at triangle
      linarith
    · have last : j - n < m := by omega
      have nx := secondTrace x hx (j - n) last
      have ny := secondTrace y hy (j - n) last
      have index : n + (j - n) = j := by omega
      rw [index] at nx ny
      rw [← sameB] at ny
      have triangle := dist_triangle (T^[j] x) (T^[j - n] (b x)) (T^[j] y)
      rw [dist_comm (T^[j - n] (b x)) (T^[j] y)] at triangle
      linarith
  have pointBound (x : X) (hx : x ∈ s) : Real.exp (orbitSum T φ (n + m) x) ≤
      Real.exp (2 * D) * Real.exp (orbitSum T φ n (a x)) * Real.exp (orbitSum T φ m (b x)) := by
    have firstEnergy := (abs_le.mp (bowen n x (a x) (firstTrace x hx))).2
    have secondEnergy := (abs_le.mp (bowen m (T^[n] x) (b x) (fun j hj => by
      rw [← Function.iterate_add_apply, Nat.add_comm j n]
      exact secondTrace x hx j hj))).2
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [orbitSum_add]
    linarith
  have maps : s.image e ⊆ t.product u := by
    intro p hp
    obtain ⟨x, hx, equal⟩ := Finset.mem_image.mp hp
    rw [← equal]
    exact Finset.mem_product.mpr ⟨memberA x hx, memberB x hx⟩
  have upper := Finset.sum_le_sum_of_injOn
    (f := fun x => Real.exp (orbitSum T φ (n + m) x))
    (g := fun p : X × X => Real.exp (2 * D) * Real.exp (orbitSum T φ n p.1) *
      Real.exp (orbitSum T φ m p.2)) e injective maps
    pointBound
    (fun _ _ _ => mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _))
  calc
    _ ≤ ∑ p ∈ t.product u, Real.exp (2 * D) * Real.exp (orbitSum T φ n p.1) *
        Real.exp (orbitSum T φ m p.2) := upper
    _ = ∑ y ∈ t, ∑ z ∈ u, Real.exp (2 * D) * Real.exp (orbitSum T φ n y) *
        Real.exp (orbitSum T φ m z) := by rw [Finset.product_eq_sprod, Finset.sum_product]
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]

end LeanShared.ThermodynamicDefinitions
