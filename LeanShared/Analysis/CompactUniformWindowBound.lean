module
public import LeanShared.Analysis.CompactUniformWindowHolder

/-! A compact base gives a common small-parameter window and uniform value
bound from actual locally uniform bounds, without parameter continuity. -/
public noncomputable section
namespace LeanShared.CompactUniformLocalHolder
open Set
open scoped NNReal

theorem window_bound
    {X Y P : Type*} [MetricSpace X] [CompactSpace X] [SeminormedAddCommGroup Y]
    (f : P → X → Y) (scale : P → ℝ≥0)
    (localBound : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ η : ℝ≥0, 0 < η ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, scale p ≤ η → ∀ y ∈ W, ‖f p y‖ ≤ B) :
    ∃ η : ℝ≥0, 0 < η ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, scale p ≤ η → ∀ x, ‖f p x‖ ≤ B := by
  have controls : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ η : ℝ≥0, 0 < η ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ p, scale p ≤ η →
        (∀ y ∈ W, ‖f p y‖ ≤ B) ∧
        ∀ y ∈ W, ∀ z ∈ W, ‖f p y-f p z‖ ≤ C*dist y z^(0:ℝ) := by
    intro x
    obtain ⟨W,openW,inside,η,hη,B,hB,bound⟩ := localBound x
    refine ⟨W,openW,inside,η,hη,B,2*B,hB,mul_nonneg (by norm_num) hB,?_⟩
    intro p hp
    refine ⟨bound p hp,fun y hy z hz => ?_⟩
    rw [Real.rpow_zero,mul_one]
    exact (norm_sub_le _ _).trans
      ((add_le_add (bound p hp y hy) (bound p hp z hz)).trans_eq (two_mul B).symm)
  obtain ⟨η,hη,B,C,hB,_,bound⟩ := window_bounds f scale 0 le_rfl controls
  exact ⟨η,hη,B,hB,fun p hp => (bound p hp).1⟩

end LeanShared.CompactUniformLocalHolder
