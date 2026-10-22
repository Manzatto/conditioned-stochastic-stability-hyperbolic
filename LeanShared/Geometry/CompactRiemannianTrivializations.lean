module
public import Mathlib.Topology.VectorBundle.Riemannian
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Positivity

/-! A continuous Riemannian metric gives a finite compact-set collection of
actual bundle trivializations with uniform forward and inverse norm bounds.
Mere fiberwise `RiemannianBundle` is not used as a continuity assertion. -/
public noncomputable section
open Set Filter Bundle
open scoped Topology
namespace LeanShared.CompactRiemannianTrivializations
variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

theorem local_bound (x : B) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x,
    y ∈ (trivializationAt F E x).baseSet ∧
    ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ ≤ C ∧
    ‖(trivializationAt F E x).symmL ℝ y‖ ≤ C := by
  obtain ⟨C,hC,forward⟩ := eventually_norm_trivializationAt_lt F E x
  obtain ⟨D,hD,inverse⟩ := eventually_norm_symmL_trivializationAt_lt F E x
  refine ⟨C+D,add_pos hC hD,?_⟩
  have inside : ∀ᶠ y in 𝓝 x, y ∈ (trivializationAt F E x).baseSet :=
    (trivializationAt F E x).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  filter_upwards [inside,forward,inverse] with y hy hf hi
  exact ⟨hy,hf.le.trans (le_add_of_nonneg_right hD.le),
    hi.le.trans (le_add_of_nonneg_left hC.le)⟩

theorem finite_cover {K : Set B} (compact : IsCompact K) :
    ∃ centers : Finset B, ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∃ x ∈ centers,
      y ∈ (trivializationAt F E x).baseSet ∧
      ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ ≤ C ∧
      ‖(trivializationAt F E x).symmL ℝ y‖ ≤ C := by
  classical
  choose c positive neighborhoods using local_bound (F := F) E
  have opens (x : B) : ∃ U : Set B, U ⊆
      {y | y ∈ (trivializationAt F E x).baseSet ∧
        ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ ≤ c x ∧
        ‖(trivializationAt F E x).symmL ℝ y‖ ≤ c x} ∧ IsOpen U ∧ x ∈ U :=
    mem_nhds_iff.mp (neighborhoods x)
  choose U subset openU member using opens
  obtain ⟨centers,covers⟩ := compact.elim_finite_subcover U openU
    (fun x _ => mem_iUnion.mpr ⟨x,member x⟩)
  let C := 1+∑ x ∈ centers, c x
  have totalPositive : 0 < C := by
    apply add_pos_of_pos_of_nonneg zero_lt_one
    exact Finset.sum_nonneg (fun x _ => (positive x).le)
  refine ⟨centers,C,totalPositive,fun y hy => ?_⟩
  obtain ⟨x,hx,inside⟩ := mem_iUnion₂.mp (covers hy)
  have hbound : c x ≤ C := by
    apply (Finset.single_le_sum (fun j _ => (positive j).le) hx).trans
    exact le_add_of_nonneg_left zero_le_one
  have facts := subset x inside
  exact ⟨x,hx,facts.1,facts.2.1.trans hbound,facts.2.2.trans hbound⟩
end LeanShared.CompactRiemannianTrivializations
