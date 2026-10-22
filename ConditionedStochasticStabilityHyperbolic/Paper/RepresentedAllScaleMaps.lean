module

public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedCubeChains

/-! Outside its validity window the chosen Whitney representation is exactly
the deterministic map. Thus its all-scale measurable realization requires no
extra noise measurability assumption; spectral conclusions still only concern
the original positive small-noise window. -/
public noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [MetricSpace Parameters]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluate : Parameters → M → M}
namespace Representation
variable (p : Representation F Parameters evaluate)

omit [FiniteDimensional ℝ E] in
theorem allScale_measurable (ε : ℝ≥0) :
    Measurable (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) := by
  by_cases h : 0 < ε ∧ ε ≤ p.window
  · exact p.actual_measurable ε h.1 h.2
  · have eq : (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) =
        (fun z => T z.1) := by
      funext z
      simp only [fixedParameters, dite_eq_right h]
      exact congrFun p.reference_map z.1
    rw [eq]
    exact T.continuous.measurable.comp measurable_fst

end Representation
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
