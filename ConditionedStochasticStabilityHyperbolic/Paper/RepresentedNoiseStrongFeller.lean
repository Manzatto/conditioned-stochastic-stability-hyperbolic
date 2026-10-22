module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise

/-! The analytic representation inherits actual-law strong Feller smoothing
inside its original positive window, without an assumption on variation in ε. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [MetricSpace Parameters]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluate : Parameters → M → M}

omit [FiniteDimensional ℝ E] in
theorem Representation.strongFeller_fixed_cube
    (p : Representation F Parameters evaluate) (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (hF : Measurable (fun z : M × FixedControl (ι := ι) =>
      evaluate (p.fixedParameters ε z.2) z.1))
    (smoothSource : ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      ∀ f : M → ℝ, Measurable f → (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) →
        Continuous (fun x => ∫ z : cube (ι := ι) ε,
          g z.val * f (F.family ε z.val x) ∂cubeVolume ε)) :
    RestrictedStrongFeller.HasStrongFellerNoise (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) hF := by
  have heq : (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) =
      (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2) := by
    funext z
    exact p.actual_fixedMap ε hε hw z.1 z.2
  simpa only [heq] using F.strongFeller_fixed_cube L ε hε (hw.trans p.window_le) smoothSource

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
