module
public import LeanShared.Dynamics.WeightedSeparatedSpanning

/-! Mapping actual separated tracing points to a Bowen-spanning family
preserves their independent weights and puts the SAME cover centers in a
slightly larger prescribed-middle cylinder. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 1600000 in
theorem spanning_middle_weight_lower (T : X → X) (φ : X → ℝ)
    (N l k : ℕ) (length : l + k ≤ N) (z : X) (ε ρ D : ℝ) (positiveε : 0 < ε)
    (s q : Finset X) (separated : Separated T univ N (3 * ε) q)
    (spans : ∀ x : X, ∃ y ∈ s, ∀ j < N, dist (T^[j] x) (T^[j] y) < ε)
    (middle : ∀ x ∈ q, ∀ j < k, dist (T^[l + j] x) (T^[j] z) < ρ)
    (bowen : ∀ x y, (∀ j < N, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ N x - orbitSum T φ N y| ≤ D) :
    Real.exp (-D) * (∑ x ∈ q, Real.exp (orbitSum T φ N x)) ≤
      ∑ y ∈ s.filter (fun y => ∀ j < k, dist (T^[l + j] y) (T^[j] z) < ε + ρ),
        Real.exp (orbitSum T φ N y) := by
  classical
  choose center member trace using spans
  have injective : Set.InjOn center q := by
    intro x hx y hy equal
    by_contra different
    obtain ⟨j, hj, far⟩ := separated.2 x hx y hy different
    have first := trace x j hj
    have second := trace y j hj
    rw [← equal] at second
    have triangle := dist_triangle (T^[j] x) (T^[j] (center x)) (T^[j] y)
    rw [dist_comm (T^[j] (center x)) (T^[j] y)] at triangle
    linarith
  have mapped : q.image center ⊆ s.filter
      (fun y => ∀ j < k, dist (T^[l + j] y) (T^[j] z) < ε + ρ) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_filter.mpr ⟨member x, fun j hj => ?_⟩
    have first := trace x (l + j) (by omega)
    have second := middle x hx j hj
    have triangle := dist_triangle (T^[l + j] (center x)) (T^[l + j] x) (T^[j] z)
    rw [dist_comm (T^[l + j] (center x)) (T^[l + j] x)] at triangle
    linarith
  have pointBound (x : X) (_ : x ∈ q) : Real.exp (-D) * Real.exp (orbitSum T φ N x) ≤
      Real.exp (orbitSum T φ N (center x)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (bowen x (center x) (trace x))).2])
  have bound := Finset.sum_le_sum_of_injOn
    (f := fun x => Real.exp (-D) * Real.exp (orbitSum T φ N x))
    (g := fun x => Real.exp (orbitSum T φ N x)) center injective mapped
    pointBound (fun _ _ _ => Real.exp_nonneg _)
  rwa [← Finset.mul_sum] at bound

end LeanShared.ThermodynamicDefinitions
