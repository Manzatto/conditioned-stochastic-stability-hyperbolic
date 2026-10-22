module

public import LeanShared.Dynamics.ExpansiveBowenWindowShrinking
public import Mathlib.Topology.MetricSpace.Thickening

/-! Fixed-radius orbit cylinders centered on compact subsets eventually lie
in any prescribed open neighbourhood. Only their time length changes;
the coarse radius remains the fixed expansivity radius. -/
public noncomputable section
open Set Function
namespace LeanShared.FiniteExpansiveWords
variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_centered_cylinder_containment (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (K U : Set X) (compact : IsCompact K) (opened : IsOpen U) (inside : K ⊆ U) :
    ∃ N : ℕ, ∀ x ∈ K, ∀ y : X,
      (∀ j < 2 * N + 1,
        dist (T^[j] y) (T^[j] ((T.symm : X → X)^[N] x)) ≤ c) →
      T^[N] y ∈ U := by
  obtain ⟨η, positive, near⟩ := compact.exists_thickening_subset_open opened inside
  obtain ⟨N, detects⟩ := exists_window_shrinking T c expansive η positive
  refine ⟨N, fun x hx y close => ?_⟩
  have distance := detects 1 y ((T.symm : X → X)^[N] x)
    (fun j hj => close j (by omega)) 0 (by omega)
  simp only [Nat.add_zero] at distance
  have cancel : (T : X → X)^[N] ((T.symm : X → X)^[N] x) = x :=
    T.right_inv.iterate N x
  rw [cancel] at distance
  exact near (Metric.mem_thickening_iff.mpr ⟨x, hx, distance⟩)

end LeanShared.FiniteExpansiveWords
