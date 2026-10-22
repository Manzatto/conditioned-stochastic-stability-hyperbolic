module

public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Conclusions
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # The manuscript's stable sets at the global theorem boundary

The stable basin of a nonempty compact basic set uses the standard condition
that its forward distance to the set tends to zero. The finite metric
approach premise of the checked control proof follows, including its n+1
index convention. No stochastic conclusion enters this definition.
-/
@[expose] public noncomputable section
open Set Filter Function Metric
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.PaperStableBasin
variable {X : Type*} [MetricSpace X]

def stableBasin (T : X → X) (Γ : Set X) : Set X :=
  {x | Γ.Nonempty ∧ Tendsto (fun n : ℕ => infDist (T^[n] x) Γ) atTop (𝓝 0)}

theorem metric_approach_of_mem_stableBasin (T : X → X) (Γ : Set X) (x : X)
    (hx : x ∈ stableBasin T Γ) :
    ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Γ, dist (T^[n + 1] x) y < r := by
  intro r hr
  have hlt : ∀ᶠ n : ℕ in atTop, infDist (T^[n] x) Γ < r := hx.2.eventually (gt_mem_nhds hr)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlt
  obtain ⟨y, hy, hd⟩ := (infDist_lt_iff hx.1).mp (hN (N + 1) (Nat.le_succ N))
  exact ⟨N, y, hy, hd⟩

/-- The unstable basin is the stable basin for the inverse homeomorphism. -/
def unstableBasin (T : X ≃ₜ X) (Γ : Set X) : Set X := stableBasin T.symm Γ

theorem metric_past_approach_of_mem_unstableBasin (T : X ≃ₜ X)
    (Γ : Set X) (x : X) (hx : x ∈ unstableBasin T Γ) :
    ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Γ, dist (T.symm^[n] x) y < r := by
  intro r hr
  obtain ⟨n, y, hy, hd⟩ := metric_approach_of_mem_stableBasin T.symm Γ x hx r hr
  exact ⟨n + 1, y, hy, hd⟩

/-- An actual heteroclinic point lies outside both basic sets. -/
def heteroclinicRelation {I : Type*} (T : X ≃ₜ X) (Λ : I → Set X)
    (i j : I) : Prop :=
  ∃ x : X, x ∈ unstableBasin T (Λ i) \ Λ i ∧ x ∈ stableBasin T (Λ j) \ Λ j

theorem metric_approaches_of_heteroclinicRelation {I : Type*}
    (T : X ≃ₜ X) (Λ : I → Set X) (i j : I)
    (h : heteroclinicRelation T Λ i j) :
    ∃ x : X,
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ j, dist (T^[n + 1] x) y < r) ∧
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Λ i, dist (T.symm^[n] x) y < r) := by
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, metric_approach_of_mem_stableBasin T (Λ j) x hy.1,
    metric_past_approach_of_mem_unstableBasin T (Λ i) x hx.1⟩

end ConditionedStochasticStabilityHyperbolic.Global.PaperStableBasin
