module
import all ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry
public import ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixEncoding

/-! The actual first greedy residual is the whole graph. This metadata is
proved from the constructed algorithm rather than added to its input. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry
open Function Relation
variable {I : Type*} [DecidableEq I] [Fintype I]

theorem first_size (edge : I → I → Prop) (pressure : I → ℝ)
    (acyclic : ∀ v, ¬TransGen edge v v) (distinct : Injective pressure)
    (positive : 0 < (ofGraph edge pressure acyclic distinct).number) :
    (ofGraph edge pressure acyclic distinct).size ⟨0, positive⟩ =
      (ofGraph edge pressure acyclic distinct).order.length := by
  rfl

theorem first_terminal (edge : I → I → Prop) (pressure : I → ℝ)
    (acyclic : ∀ v, ¬TransGen edge v v) (distinct : Injective pressure)
    (positive : 0 < (ofGraph edge pressure acyclic distinct).number) :
    ((ofGraph edge pressure acyclic distinct).terminal ⟨0, positive⟩).val + 1 =
      (ofGraph edge pressure acyclic distinct).order.length := by
  rw [Data.terminal_size]
  exact first_size edge pressure acyclic distinct positive
end ConditionedStochasticStabilityHyperbolic.Global.GreedyPrefixGeometry
