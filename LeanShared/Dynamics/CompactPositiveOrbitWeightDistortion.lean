module

public import LeanShared.Dynamics.CompactPositiveWeightDistortion
public import Mathlib.Tactic.Ring

/-! One actual near-core radius controls all finite weight products, with
only an arbitrarily prescribed exponential loss in their length. -/
public noncomputable section
namespace LeanShared.CompactPositiveOrbitWeightDistortion
open Set
variable {X : Type*} [PseudoMetricSpace X]

theorem exists_radius (K : Set X) (compact : IsCompact K) (g : X → ℝ)
    (continuous : Continuous g) (positive : ∀ x ∈ K, 0 < g x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℕ, ∀ x y : ℕ → X,
      (∀ i < n, x i ∈ K) → (∀ i < n, dist (x i) (y i) < ρ) →
      0 < (∏ i ∈ Finset.range n, g (y i)) ∧
      Real.exp (-ε * n) * (∏ i ∈ Finset.range n, g (x i)) ≤ ∏ i ∈ Finset.range n, g (y i) := by
  obtain ⟨ρ, hρ, nearby⟩ := CompactPositiveWeightDistortion.exists_radius K compact g continuous positive ε hε
  refine ⟨ρ, hρ, fun n x y core close => ?_⟩
  have point (i : ℕ) (hi : i ∈ Finset.range n) := nearby (x i) (core i (Finset.mem_range.mp hi))
    (y i) (close i (Finset.mem_range.mp hi))
  refine ⟨Finset.prod_pos (fun i hi => (point i hi).1), ?_⟩
  have product := Finset.prod_le_prod₀
    (fun i hi => mul_nonneg (Real.exp_pos _).le (positive _ (core i (Finset.mem_range.mp hi))).le)
    (fun i hi => (point i hi).2)
  have identity : (∏ i ∈ Finset.range n, (Real.exp (-ε) * g (x i))) =
      Real.exp (-ε * n) * (∏ i ∈ Finset.range n, g (x i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [identity] at product
  exact product

end LeanShared.CompactPositiveOrbitWeightDistortion
