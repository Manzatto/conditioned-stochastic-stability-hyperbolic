module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcome
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
meta import Lean.LibrarySuggestions.Basic

/-! Scalar orders and the stable framing dimension used by the native carrier constructions. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativeProducerOrders"

public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcomeProducer
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet

variable {E : Type*} {M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

/-- The scalar orders of the native local construction. -/
theorem native_orders {r : ℝ} (hr : 1 < r) :
    ∃ α t s δ : ℝ, 0 < α ∧ α < 1 ∧ α < r - 1 ∧ α + 1 < r ∧ 0 < t ∧ s < 0 ∧ 0 < δ ∧
      δ + δ < t ∧ t - s + (δ + δ) < α := by
  refine ⟨min (1/2) ((r - 1) / 2), min (1/2) ((r - 1) / 2) / 4, -(min (1/2) ((r - 1) / 2) / 8),
    min (1/2) ((r - 1) / 2) / 16, ?_⟩
  have pos : 0 < min (1/2 : ℝ) ((r - 1) / 2) := lt_min (by norm_num) (by linarith)
  have le1 : min (1/2 : ℝ) ((r - 1) / 2) ≤ 1/2 := min_le_left _ _
  have le2 : min (1/2 : ℝ) ((r - 1) / 2) ≤ (r - 1) / 2 := min_le_right _ _
  refine ⟨pos, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

theorem framing_stable_pos {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
    (a : IsometricFraming h) {x : M} (hx : x ∈ Λ) (stable : 0 < Module.finrank ℝ (h.stable x)) :
    0 < a.stableDimension := by
  rw [← (a.stable ⟨x, hx⟩).toLinearEquiv.finrank_eq, finrank_euclideanSpace_fin] at stable
  exact stable

end ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcomeProducer
