module

public import ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixReachability

/-! # Actual HG2 selected-prefix graph and pressure data

On the retained basic-set subtype, no cycles and injective pressure determine
the greedy blocks. For every selected block this theorem constructs its exact
finite prefix root, strict pressure gap at all other prefix layers and graph
accessibility for its entire predecessor basin. It supplies the combinatorial
inputs of the actual prefix QEM and stable-basin consumers.
-/
@[expose] public noncomputable section
open Set Relation
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualHG2Selection
open LeanShared PressureBlocks PressureTopologicalOrder PressureFiltrationSource
open PressurePrefixReachability
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_actual_HG2_selected_prefix
    (edge : I → I → Prop) (pressure : I → ℝ)
    (hacyclic : ∀ v, ¬TransGen edge v v) (hdistinct : Function.Injective pressure)
    (n : ℕ) (b : Block I) (tail : List (Block I))
    (hdrop : (blocks edge pressure Finset.univ).drop n = b :: tail) :
    let hWF := wellFounded_of_acyclic edge hacyclic
    let L := blockOrder edge pressure hWF (b :: tail)
    ∃ R' : Finset I, SelectionTrace edge pressure R' (b :: tail) ∧
      ForwardClosed edge R' ∧ b.root ∈ R' ∧
      ∃ j : Fin L.length, reversedVertex L j = b.root ∧
        (∀ i : Fin L.length, i ≠ j → pressure (reversedVertex L i) < pressure b.root) ∧
        ∀ i : Fin L.length, reversedVertex L i ∈ b.members →
          ReflTransGen (fun a c : Fin L.length => edge (reversedVertex L a) (reversedVertex L c)) i j := by
  dsimp only
  obtain ⟨R', _, hclosed, htrace⟩ := exists_forward_closed_residual edge pressure Finset.univ
    (blocks edge pressure Finset.univ) (blocks_selectionTrace edge pressure Finset.univ)
    (by intro x hx y hxy; exact Finset.mem_univ y) n
  have ht : SelectionTrace edge pressure R' (b :: tail) := hdrop ▸ htrace
  refine ⟨R', ht, hclosed, (PressureResidualBounds.head_root_maximal ht).1, ?_⟩
  exact exists_actual_selected_prefix_root edge pressure (wellFounded_of_acyclic edge hacyclic)
    R' b tail ht hclosed (fun _ _ _ _ he => hdistinct he)

end ConditionedStochasticStabilityHyperbolic.Global.ActualHG2Selection
