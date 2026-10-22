module
public import ConditionedStochasticStabilityHyperbolic.Global.GreedySelectedIntervals
import all ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixEncoding

/-! Exact labelled intervals in the final terminal/root encoding. -/
public noncomputable section
open Set Relation
namespace ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry.Data
open LeanShared PressureFiltrationSource DerivedHG2Basins
variable {I : Type*} {edge : I → I → Prop} {pressure : I → ℝ}
  (d : GreedyPrefixGeometry.Data edge pressure)

theorem selected_adjacent (s q : Fin d.number) (next : q.val = s.val + 1) :
    (d.terminal q).val + 1 = (d.selectedRoot s).val := by
  simpa only [terminal_size, selectedRoot, Fin.val_cast] using d.next_size_eq_root s q next

theorem selected_last_zero (s : Fin d.number) (last : s.val + 1 = d.number) :
    (d.selectedRoot s).val = 0 := by
  simpa only [selectedRoot, Fin.val_cast] using d.last_root_zero s last

/-- Every index in [selectedRoot s, terminal s] is assigned to that
prescribed root, with an actual path entirely inside its prefix. -/
theorem selected_interval_reachable (s : Fin d.number)
    (i : Fin ((d.terminal s).val + 1)) (lower : (d.selectedRoot s).val ≤ i.val) :
    ReflTransGen (fun a b : Fin ((d.terminal s).val + 1) =>
      edge (reversedVertex d.order (originalIndex a))
        (reversedVertex d.order (originalIndex b))) i (d.selectedRoot s) := by
  have upper : i.val < d.size s := by simpa only [terminal_size] using i.isLt
  have low : (d.root s).val ≤ i.val := by simpa only [selectedRoot, Fin.val_cast] using lower
  have path := d.interval_reachable s (originalIndex i) low upper
  have lifted := ReflTransGen.lift
    (p := fun a b : Fin ((d.terminal s).val + 1) =>
      edge (reversedVertex d.order (originalIndex a)) (reversedVertex d.order (originalIndex b)))
    (Fin.cast (d.terminal_size s).symm) (fun _ _ e => e)
    ⟨i.val, upper⟩ (d.root s) path
  have start : Fin.cast (d.terminal_size s).symm ⟨i.val, upper⟩ = i := Fin.ext rfl
  dsimp only [Function.onFun] at lifted
  rw [start] at lifted
  exact lifted
end ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry.Data
