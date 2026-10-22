module
public import LeanShared.Analysis.CompactUniformLocalHolder

/-! Pointwise positive windows and parameter-uniform local controls produce
one global positive window BEFORE every parameter. This uses compactness,
not continuity in the scale or parameter. -/
public noncomputable section
namespace LeanShared.CompactUniformLocalHolder
open Set
open scoped NNReal

theorem window_bounds
    {X Y P : Type*} [MetricSpace X] [CompactSpace X] [SeminormedAddCommGroup Y]
    (f : P → X → Y) (scale : P → ℝ≥0) (a : ℝ) (ha : 0 ≤ a)
    (localBound : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ η : ℝ≥0, 0 < η ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ p, scale p ≤ η →
        (∀ y ∈ W, ‖f p y‖ ≤ B) ∧
        ∀ y ∈ W, ∀ z ∈ W, ‖f p y-f p z‖ ≤ C*dist y z^a) :
    ∃ η : ℝ≥0, 0 < η ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ p, scale p ≤ η →
      (∀ x, ‖f p x‖ ≤ B) ∧ ∀ x y, ‖f p x-f p y‖ ≤ C*dist x y^a := by
  classical
  choose W openW member window positive B C hB hC facts using localBound
  obtain ⟨s,cover⟩ := isCompact_univ.elim_finite_subcover W openW
    (fun x _ => mem_iUnion.mpr ⟨x,member x⟩)
  have common (t : Finset X) : ∃ η : ℝ≥0, 0 < η ∧ ∀ i ∈ t, η ≤ window i := by
    induction t using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert i t notMem ih =>
      obtain ⟨η,hη,small⟩ := ih
      refine ⟨min η (window i),lt_min hη (positive i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (small j hj)
  obtain ⟨η,hη,small⟩ := common s
  let Q := {p : P // scale p ≤ η}
  have localRestricted : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ b c : ℝ, 0 ≤ b ∧ 0 ≤ c ∧ ∀ p : Q,
        (∀ y ∈ U, ‖f p.val y‖ ≤ b) ∧
        ∀ y ∈ U, ∀ z ∈ U, ‖f p.val y-f p.val z‖ ≤ c*dist y z^a := by
    intro x
    rcases mem_iUnion.mp (cover (mem_univ x)) with ⟨i,h⟩
    rcases mem_iUnion.mp h with ⟨hi,hx⟩
    refine ⟨W i,openW i,hx,B i,C i,hB i,hC i,?_⟩
    intro p
    exact facts i p.val (p.property.trans (small i hi))
  obtain ⟨b,c,hb,hc,global⟩ := bounds (fun p : Q => f p.val) a ha localRestricted
  exact ⟨η,hη,b,c,hb,hc,fun p hp => global ⟨p,hp⟩⟩

end LeanShared.CompactUniformLocalHolder
