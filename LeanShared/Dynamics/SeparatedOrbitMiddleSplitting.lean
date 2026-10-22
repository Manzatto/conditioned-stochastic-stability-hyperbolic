module
public import LeanShared.Dynamics.SeparatedOrbitSplitting

/-! A separated family with a prescribed middle orbit segment is coded
injectively by its prefix and suffix cover centers. This gives the weighted
cylinder estimate used to construct actual Gibbs probabilities. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 2000000 in
theorem weighted_middle_splitting (T : X → X) (φ : X → ℝ)
    (ε D : ℝ) (positiveε : 0 < ε) (n k m : ℕ) (s t u : Finset X) (z : X)
    (separated : Separated T univ (n + k + m) (3 * ε) s)
    (a b : X → X) (memberA : ∀ x ∈ s, a x ∈ t) (memberB : ∀ x ∈ s, b x ∈ u)
    (firstTrace : ∀ x ∈ s, ∀ j < n, dist (T^[j] x) (T^[j] (a x)) < ε)
    (middleTrace : ∀ x ∈ s, ∀ j < k, dist (T^[n + j] x) (T^[j] z) < ε)
    (lastTrace : ∀ x ∈ s, ∀ j < m, dist (T^[n + k + j] x) (T^[j] (b x)) < ε)
    (bowen : ∀ h x y, (∀ j < h, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ h x - orbitSum T φ h y| ≤ D) :
    (∑ x ∈ s, Real.exp (orbitSum T φ (n + k + m) x)) ≤
      Real.exp (3 * D + orbitSum T φ k z) *
        (∑ y ∈ t, Real.exp (orbitSum T φ n y)) *
        (∑ y ∈ u, Real.exp (orbitSum T φ m y)) := by
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
    · by_cases middle : j < n + k
      · have hjk : j - n < k := by omega
        have index : n + (j - n) = j := by omega
        have nx := middleTrace x hx (j - n) hjk
        have ny := middleTrace y hy (j - n) hjk
        rw [index] at nx ny
        have triangle := dist_triangle (T^[j] x) (T^[j - n] z) (T^[j] y)
        rw [dist_comm (T^[j - n] z) (T^[j] y)] at triangle
        linarith
      · have hjm : j - (n + k) < m := by omega
        have index : n + k + (j - (n + k)) = j := by omega
        have nx := lastTrace x hx (j - (n + k)) hjm
        have ny := lastTrace y hy (j - (n + k)) hjm
        rw [index] at nx ny
        rw [← sameB] at ny
        have triangle := dist_triangle (T^[j] x) (T^[j - (n + k)] (b x)) (T^[j] y)
        rw [dist_comm (T^[j - (n + k)] (b x)) (T^[j] y)] at triangle
        linarith
  have pointBound (x : X) (hx : x ∈ s) : Real.exp (orbitSum T φ (n + k + m) x) ≤
      Real.exp (3 * D + orbitSum T φ k z) * Real.exp (orbitSum T φ n (a x)) *
        Real.exp (orbitSum T φ m (b x)) := by
    have prefixEnergy := (abs_le.mp (bowen n x (a x) (firstTrace x hx))).2
    have middle := (abs_le.mp (bowen k (T^[n] x) z (fun j hj => by
      rw [← Function.iterate_add_apply, Nat.add_comm j n]
      exact middleTrace x hx j hj))).2
    have suffixEnergy := (abs_le.mp (bowen m (T^[n + k] x) (b x) (fun j hj => by
      rw [← Function.iterate_add_apply, Nat.add_comm j (n + k)]
      exact lastTrace x hx j hj))).2
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [orbitSum_add, orbitSum_add]
    linarith
  have maps : s.image e ⊆ t.product u := by
    intro p hp
    obtain ⟨x, hx, equal⟩ := Finset.mem_image.mp hp
    rw [← equal]
    exact Finset.mem_product.mpr ⟨memberA x hx, memberB x hx⟩
  have upper := Finset.sum_le_sum_of_injOn
    (f := fun x => Real.exp (orbitSum T φ (n + k + m) x))
    (g := fun p : X × X => Real.exp (3 * D + orbitSum T φ k z) *
      Real.exp (orbitSum T φ n p.1) * Real.exp (orbitSum T φ m p.2))
    e injective maps pointBound
    (fun _ _ _ => mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _))
  calc
    _ ≤ ∑ p ∈ t.product u, Real.exp (3 * D + orbitSum T φ k z) *
        Real.exp (orbitSum T φ n p.1) * Real.exp (orbitSum T φ m p.2) := upper
    _ = ∑ y ∈ t, ∑ v ∈ u, Real.exp (3 * D + orbitSum T φ k z) *
        Real.exp (orbitSum T φ n y) * Real.exp (orbitSum T φ m v) := by
      rw [Finset.product_eq_sprod, Finset.sum_product]
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]

end LeanShared.ThermodynamicDefinitions
