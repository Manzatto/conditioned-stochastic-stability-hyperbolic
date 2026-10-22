module
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Local parameter-uniform value and Holder controls globalize on a compact
metric space. The parameter carries NO topology; continuity in noise scale
is neither required nor inferred. -/
public noncomputable section
namespace LeanShared.CompactUniformLocalHolder
open Set Metric

theorem bounds
    {X Y P : Type*} [MetricSpace X] [CompactSpace X] [SeminormedAddCommGroup Y]
    (f : P → X → Y) (a : ℝ) (ha : 0 ≤ a)
    (localBound : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ p,
        (∀ y ∈ W, ‖f p y‖ ≤ B) ∧
        ∀ y ∈ W, ∀ z ∈ W, ‖f p y-f p z‖ ≤ C*dist y z^a) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ p,
      (∀ x, ‖f p x‖ ≤ B) ∧ ∀ x y, ‖f p x-f p y‖ ≤ C*dist x y^a := by
  classical
  choose W openW member B C hB hC facts using localBound
  obtain ⟨s,cover⟩ := isCompact_univ.elim_finite_subcover W openW
    (fun x _ => mem_iUnion.mpr ⟨x,member x⟩)
  have chosen (x : X) : ∃ i ∈ s, x ∈ W i := by
    rcases mem_iUnion.mp (cover (mem_univ x)) with ⟨i,h⟩
    rcases mem_iUnion.mp h with ⟨hi,hx⟩
    exact ⟨i,hi,hx⟩
  let U : (↑s : Type _) → Set X := fun i => W i.val
  have coverU : (univ : Set X) ⊆ ⋃ i, U i := by
    intro x _
    obtain ⟨i,hi,hx⟩ := chosen x
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hx⟩
  obtain ⟨δ,hδ,balls⟩ := lebesgue_number_lemma_of_metric (c := U) isCompact_univ (fun i => openW i.val) coverU
  let Bsum := ∑ i ∈ s, B i
  let Csum := ∑ i ∈ s, C i
  have hBs : 0 ≤ Bsum := Finset.sum_nonneg (fun i _ => hB i)
  have hCs : 0 ≤ Csum := Finset.sum_nonneg (fun i _ => hC i)
  have value (p : P) (x : X) : ‖f p x‖ ≤ Bsum := by
    obtain ⟨i,hi,hx⟩ := chosen x
    exact ((facts i p).1 x hx).trans (Finset.single_le_sum (fun j _ => hB j) hi)
  let H := max Csum ((2*Bsum)/δ^a)
  have hH : 0 ≤ H := hCs.trans (le_max_left _ _)
  refine ⟨Bsum,H,hBs,hH,fun p => ⟨value p,fun x y => ?_⟩⟩
  by_cases near : dist x y < δ
  · obtain ⟨i,ball⟩ := balls x (mem_univ x)
    have hx : x ∈ U i := ball (mem_ball_self hδ)
    have hy : y ∈ U i := ball (by simpa only [mem_ball,dist_comm] using near)
    have localEstimate := (facts i.val p).2 x hx y hy
    have constant : C i.val ≤ H :=
      (Finset.single_le_sum (fun j _ => hC j) i.property).trans (le_max_left _ _)
    exact localEstimate.trans (mul_le_mul_of_nonneg_right constant (Real.rpow_nonneg dist_nonneg _))
  · have far : δ ≤ dist x y := le_of_not_gt near
    have power : δ^a ≤ dist x y^a := Real.rpow_le_rpow hδ.le far ha
    have positive : 0 < δ^a := Real.rpow_pos_of_pos hδ _
    have triangle : ‖f p x-f p y‖ ≤ 2*Bsum :=
      (norm_sub_le _ _).trans ((add_le_add (value p x) (value p y)).trans_eq (two_mul Bsum).symm)
    calc
      _ ≤ 2*Bsum := triangle
      _ = ((2*Bsum)/δ^a)*δ^a := (div_mul_cancel₀ _ positive.ne').symm
      _ ≤ ((2*Bsum)/δ^a)*dist x y^a :=
        mul_le_mul_of_nonneg_left power (div_nonneg (mul_nonneg (by norm_num) hBs) positive.le)
      _ ≤ H*dist x y^a := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)

end LeanShared.CompactUniformLocalHolder
