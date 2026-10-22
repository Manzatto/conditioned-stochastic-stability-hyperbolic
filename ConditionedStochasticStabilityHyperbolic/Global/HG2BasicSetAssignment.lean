module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualHG2Selection
public import Mathlib.Data.List.TakeDrop

/-! # Every retained basic set has its actual HG2 selected prefix

For each retained basic set the checked greedy algorithm selects its block,
its residual prefix and the two literal finite indices for the starting basic
set and selected root. Strict pressure separation and internal accessibility
are outputs. This is the assignment used for the all-stable-start conclusion.
-/
@[expose] public noncomputable section
open Set Relation
namespace ConditionedStochasticStabilityHyperbolic.Global.HG2BasicSetAssignment
open LeanShared PressureBlocks PressureTopologicalOrder PressureFiltrationSource
open PressurePrefixSelection PressurePrefixReachability ActualHG2Selection
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_actual_prefix_for_each_retained_basic_set
    (edge : I → I → Prop) (pressure : I → ℝ)
    (hacyclic : ∀ v, ¬TransGen edge v v) (hdistinct : Function.Injective pressure) (v : I) :
    ∃ n : ℕ, ∃ b : Block I, ∃ tail : List (Block I),
      (blocks edge pressure Finset.univ).drop n = b :: tail ∧ v ∈ b.members ∧
      let L := blockOrder edge pressure (wellFounded_of_acyclic edge hacyclic) (b :: tail)
      ∃ start root : Fin L.length,
        reversedVertex L start = v ∧ reversedVertex L root = b.root ∧
        (∀ i : Fin L.length, i ≠ root → pressure (reversedVertex L i) < pressure b.root) ∧
        ReflTransGen (fun a c : Fin L.length => edge (reversedVertex L a) (reversedVertex L c)) start root := by
  obtain ⟨b, ⟨hb, hvb⟩, _⟩ := exists_unique_block_univ edge pressure v
  obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp hb
  have hdrop : (blocks edge pressure Finset.univ).drop idx.val =
      b :: (blocks edge pressure Finset.univ).drop (idx.val + 1) := by
    have hd := List.drop_eq_getElem_cons idx.isLt
    simpa only [← List.get_eq_getElem, hidx] using hd
  let tail := (blocks edge pressure Finset.univ).drop (idx.val + 1)
  obtain ⟨R', ht, hclosed, _, root, hroot, hpressure, hreach⟩ :=
    exists_actual_HG2_selected_prefix edge pressure hacyclic hdistinct idx.val b tail hdrop
  let L := blockOrder edge pressure (wellFounded_of_acyclic edge hacyclic) (b :: tail)
  have hvL : v ∈ L := (mem_blockOrder edge pressure _ _ _).mpr ⟨b, by simp, hvb⟩
  obtain ⟨start, hstart⟩ := exists_reversed_prefix_index [] L v hvL
  simp only [List.nil_append] at hstart
  refine ⟨idx.val, b, tail, hdrop, hvb, start, root, hstart, hroot, hpressure, ?_⟩
  exact hreach start (hstart.symm ▸ hvb)

end ConditionedStochasticStabilityHyperbolic.Global.HG2BasicSetAssignment
