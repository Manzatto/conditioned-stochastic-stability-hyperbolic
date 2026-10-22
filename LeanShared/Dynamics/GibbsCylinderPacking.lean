module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Actual separated orbit cylinders are disjoint. Gibbs estimates therefore
control the mass of their union by the same finite weighted orbit sum.
The complementary covering estimate applies to arbitrary prescribed subsets. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

 theorem gibbs_cover_weight (T : X → X) (φ : X → ℝ) (ν : Measure X)
    (K : Set X) (s : Finset X) (n : ℕ) (ρ H P : ℝ)
    (cover : ∀ x ∈ K, ∃ y ∈ s, ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ ρ)
    (upper : ∀ y ∈ s, ν {x | ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ ρ} ≤
      ENNReal.ofReal (H * Real.exp (orbitSum T φ n y - (n : ℝ) * P))) :
    ν K ≤ ∑ y ∈ s, ENNReal.ofReal
      (H * Real.exp (orbitSum T φ n y - (n : ℝ) * P)) := by
  have covered : K ⊆ ⋃ y ∈ s, {x | ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ ρ} := by
    intro x hx
    obtain ⟨y, hy, near⟩ := cover x hx
    exact mem_iUnion₂.mpr ⟨y, hy, near⟩
  exact (measure_mono covered).trans
    ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum upper))

 theorem gibbs_packing_weight (T : X → X) (φ : X → ℝ) (ν : Measure X)
    (K U : Set X) (s : Finset X) (n : ℕ) (ρ A P : ℝ)
    (separated : Separated T K n (2 * ρ) s)
    (measurable : ∀ y ∈ s, MeasurableSet
      {x | ∀ j < n, dist (T^[j] x) (T^[j] y) < ρ})
    (inside : ∀ y ∈ s, {x | ∀ j < n, dist (T^[j] x) (T^[j] y) < ρ} ⊆ U)
    (lower : ∀ y ∈ s, ENNReal.ofReal
      (A * Real.exp (orbitSum T φ n y - (n : ℝ) * P)) ≤
      ν {x | ∀ j < n, dist (T^[j] x) (T^[j] y) < ρ}) :
    (∑ y ∈ s, ENNReal.ofReal
      (A * Real.exp (orbitSum T φ n y - (n : ℝ) * P))) ≤ ν U := by
  let B (y : X) := {x | ∀ j < n, dist (T^[j] x) (T^[j] y) < ρ}
  have disjoint : PairwiseDisjoint (s : Set X) B := by
    intro x hx y hy different
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    obtain ⟨j, hj, apart⟩ := separated.2 x hx y hy different
    have triangle := dist_triangle (T^[j] x) (T^[j] z) (T^[j] y)
    have first := hzx j hj
    have second := hzy j hj
    rw [dist_comm (T^[j] z) (T^[j] x)] at first
    linarith
  have contained : (⋃ y ∈ s, B y) ⊆ U := by
    intro x hx
    obtain ⟨y, hy, near⟩ := mem_iUnion₂.mp hx
    exact inside y hy near
  calc
    _ ≤ ∑ y ∈ s, ν (B y) := Finset.sum_le_sum lower
    _ = ν (⋃ y ∈ s, B y) := (measure_biUnion_finset disjoint measurable).symm
    _ ≤ ν U := measure_mono contained

end LeanShared.ThermodynamicDefinitions
