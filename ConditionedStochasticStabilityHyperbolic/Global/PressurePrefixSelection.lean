module

public import ConditionedStochasticStabilityHyperbolic.Global.PressureFiltrationSource
public import ConditionedStochasticStabilityHyperbolic.Global.PressureResidualBounds

/-! # Literal reversed prefixes are the greedy pressure residuals

The actual graph-compatible order has contiguous predecessor blocks. Removing
its initial blocks therefore leaves exactly a prefix of the reversed filtration
order. The following proof identifies its vertices with the greedy residual,
so the selected root's strict pressure bound applies to every subordinate
literal layer of that prefix.
-/
@[expose] public noncomputable section
open Set Relation
namespace ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixSelection
open LeanShared PressureBlocks PressureTopologicalOrder PressureFiltrationSource
variable {I : Type*} [DecidableEq I]

omit [DecidableEq I] in
/-- A reversed index in the final segment belongs to that segment. -/
theorem reversed_prefix_mem_suffix (before suffix : List I) (i : Fin suffix.length) :
    reversedVertex (before ++ suffix)
      ⟨i.val, by simp only [List.length_append]; omega⟩ ∈ suffix := by
  unfold reversedVertex
  rw [List.get_eq_getElem, List.getElem_append_right (by simp only [List.length_append]; omega)]
  exact List.getElem_mem _

omit [DecidableEq I] in
theorem reversed_prefix_mem_of_split (L before suffix : List I) (hs : L = before ++ suffix)
    (i : Fin suffix.length) (hi : i.val < L.length) :
    reversedVertex L ⟨i.val, hi⟩ ∈ suffix := by
  subst L
  exact reversed_prefix_mem_suffix before suffix i

omit [DecidableEq I] in
theorem exists_reversed_prefix_index (before suffix : List I) (v : I) (hv : v ∈ suffix) :
    ∃ i : Fin suffix.length, reversedVertex (before ++ suffix)
      ⟨i.val, by simp only [List.length_append]; omega⟩ = v := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
  refine ⟨⟨suffix.length - 1 - j.val, by omega⟩, ?_⟩
  unfold reversedVertex
  rw [List.get_eq_getElem, List.getElem_append_right (by simp only [List.length_append]; omega)]
  have hn : (before ++ suffix).length - 1 - (suffix.length - 1 - j.val) - before.length = j.val := by
    simp only [List.length_append]
    omega
  simpa only [hn, ← List.get_eq_getElem] using hj

/-- Block ordering respects list splitting, without any new graph premise. -/
theorem blockOrder_take_drop (edge : I → I → Prop) (pressure : I → ℝ)
    (hWF : WellFounded (TransGen edge)) (L : List (Block I)) (n : ℕ) :
    blockOrder edge pressure hWF L =
      blockOrder edge pressure hWF (L.take n) ++ blockOrder edge pressure hWF (L.drop n) := by
  unfold blockOrder
  rw [← List.flatMap_append, List.take_append_drop]

/-- Every literal layer in the reversed suffix is an actual residual vertex;
its pressure is strictly below the selected head root unless it is that root.
The residual and the vertex identification are both derived from the trace. -/
theorem exists_literal_prefix_residual
    (edge : I → I → Prop) (pressure : I → ℝ) (hWF : WellFounded (TransGen edge))
    (R : Finset I) (L : List (Block I)) (htrace : SelectionTrace edge pressure R L)
    (n : ℕ) (b : Block I) (tail : List (Block I)) (hdrop : L.drop n = b :: tail)
    (hdistinct : Set.InjOn pressure (R : Set I)) :
    ∃ R' : Finset I, R' ⊆ R ∧ b.root ∈ R' ∧
      ∀ i : Fin (blockOrder edge pressure hWF (L.drop n)).length,
        let v := reversedVertex (blockOrder edge pressure hWF L)
          ⟨i.val, by
            have hs := blockOrder_take_drop edge pressure hWF L n
            rw [hs, List.length_append]
            omega⟩
        v ∈ R' ∧ (v ≠ b.root → pressure v < pressure b.root) := by
  obtain ⟨R', hsub, ht⟩ := PressureResidualBounds.exists_residual_trace htrace n
  have ht' : SelectionTrace edge pressure R' (b :: tail) := hdrop ▸ ht
  have hroot := (PressureResidualBounds.head_root_maximal ht').1
  refine ⟨R', hsub, hroot, ?_⟩
  intro i
  dsimp only
  have hmem : reversedVertex (blockOrder edge pressure hWF L)
      ⟨i.val, by
        have hs := blockOrder_take_drop edge pressure hWF L n
        rw [hs, List.length_append]
        omega⟩ ∈ blockOrder edge pressure hWF (L.drop n) := by
    exact reversed_prefix_mem_of_split _ _ _
      (blockOrder_take_drop edge pressure hWF L n) i _
  have hres : reversedVertex (blockOrder edge pressure hWF L)
      ⟨i.val, by
        have hs := blockOrder_take_drop edge pressure hWF L n
        rw [hs, List.length_append]
        omega⟩ ∈ R' := by
    exact (ht.covers _).mp ((mem_blockOrder edge pressure hWF _ _).mp hmem)
  refine ⟨hres, fun hne => ?_⟩
  exact PressureResidualBounds.pressure_lt_selected_root ht'
    (fun x hx y hy he => hdistinct (hsub hx) (hsub hy) he) _ hres hne

omit [DecidableEq I] in
theorem reversedVertex_injective (L : List I) (hL : L.Nodup) :
    Function.Injective (reversedVertex L) := by
  intro i j hij
  have he := hL.get_inj_iff.mp hij
  have hv := congrArg Fin.val he
  apply Fin.ext
  change L.length - 1 - i.val = L.length - 1 - j.val at hv
  omega

omit [DecidableEq I] in
theorem reversedVertex_append_suffix (before suffix : List I) (i : Fin suffix.length) :
    reversedVertex (before ++ suffix)
      ⟨i.val, by simp only [List.length_append]; omega⟩ = reversedVertex suffix i := by
  unfold reversedVertex
  rw [List.get_eq_getElem, List.getElem_append_right (by simp only [List.length_append]; omega),
    List.get_eq_getElem]
  congr 1
  simp only [List.length_append]
  omega

/-- Each greedy residual has one actual finite layer index for its selected
root and strictly smaller pressure at every other layer index. -/
theorem exists_selected_root_in_residual_order
    (edge : I → I → Prop) (pressure : I → ℝ) (hWF : WellFounded (TransGen edge))
    (R : Finset I) (b : Block I) (tail : List (Block I))
    (ht : SelectionTrace edge pressure R (b :: tail))
    (hdistinct : Set.InjOn pressure (R : Set I)) :
    ∃ j : Fin (blockOrder edge pressure hWF (b :: tail)).length,
      reversedVertex (blockOrder edge pressure hWF (b :: tail)) j = b.root ∧
      ∀ i : Fin (blockOrder edge pressure hWF (b :: tail)).length, i ≠ j →
        pressure (reversedVertex (blockOrder edge pressure hWF (b :: tail)) i) < pressure b.root := by
  have hroot := (PressureResidualBounds.head_root_maximal ht).1
  have hmem : b.root ∈ blockOrder edge pressure hWF (b :: tail) :=
    (mem_blockOrder edge pressure hWF _ _).mpr ((ht.covers _).mpr hroot)
  obtain ⟨j, hj⟩ := exists_reversed_prefix_index [] _ b.root hmem
  simp only [List.nil_append] at hj
  refine ⟨j, hj, ?_⟩
  intro i hij
  have hi : reversedVertex (blockOrder edge pressure hWF (b :: tail)) i ∈ R :=
    (ht.covers _).mp ((mem_blockOrder edge pressure hWF _ _).mp (List.get_mem _ _))
  apply PressureResidualBounds.pressure_lt_selected_root ht hdistinct _ hi
  intro he
  exact hij (reversedVertex_injective _ (BlockTrace.nodup ht hWF) (he.trans hj.symm))

end ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixSelection
