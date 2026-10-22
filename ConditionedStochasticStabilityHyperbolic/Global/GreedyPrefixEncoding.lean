module

public import ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry
public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Basins

/-! Encode the constructed residual sizes as the literal terminal/root
indices used by the checked HG2 basin application. -/
public noncomputable section
open Set Relation
namespace ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry.Data
open LeanShared PressureFiltrationSource DerivedHG2Basins
variable {I : Type*} {edge : I → I → Prop} {pressure : I → ℝ}
  (d : GreedyPrefixGeometry.Data edge pressure)

def terminal (s : Fin d.number) : Fin d.order.length :=
  ⟨d.size s - 1, by have hp := d.size_positive s; have hb := d.size_le s; omega⟩

theorem terminal_size (s : Fin d.number) : (d.terminal s).val + 1 = d.size s := by
  dsimp only [terminal]
  have hp := d.size_positive s
  omega

def selectedRoot (s : Fin d.number) : Fin ((d.terminal s).val + 1) :=
  Fin.cast (d.terminal_size s).symm (d.root s)

private def fromSize (s : Fin d.number) (i : Fin (d.size s)) : Fin ((d.terminal s).val + 1) :=
  Fin.cast (d.terminal_size s).symm i

/-- Later residual prefixes lie wholly below the earlier selected root. -/
theorem selected_order : ∀ s q : Fin d.number, s < q →
    (d.terminal q).val + 1 ≤ (d.selectedRoot s).val := by
  intro s q less
  simpa only [terminal_size, selectedRoot, Fin.val_cast] using d.root_above_later s q less

/-- Every original basic index is assigned inside its actual selected prefix. -/
theorem selected_assignment (j : Fin d.order.length) :
    ∃ s : Fin d.number, ∃ i : Fin ((d.terminal s).val + 1),
      j = originalIndex i ∧
      ReflTransGen (fun a b : Fin ((d.terminal s).val + 1) =>
        edge (reversedVertex d.order (originalIndex a))
          (reversedVertex d.order (originalIndex b))) i (d.selectedRoot s) := by
  obtain ⟨s, i, same, path⟩ := d.assignment j
  refine ⟨s, d.fromSize s i, ?_, ?_⟩
  · apply Fin.ext
    exact same
  · exact ReflTransGen.lift (d.fromSize s) (fun a b e => e) i (d.root s) path

/-- The selected root strictly dominates all other layers of its prefix. -/
theorem selected_pressure_gap (s : Fin d.number)
    (i : Fin ((d.terminal s).val + 1)) (different : i ≠ d.selectedRoot s) :
    pressure (reversedVertex d.order (originalIndex i)) <
      pressure (reversedVertex d.order (originalIndex (d.selectedRoot s))) := by
  let old := Fin.cast (d.terminal_size s) i
  have ne : old ≠ d.root s := by
    intro same
    apply different
    apply Fin.ext
    have values := congrArg Fin.val same
    simpa only [old, selectedRoot, Fin.val_cast] using values
  exact d.pressure_gap s old ne

end ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry.Data
