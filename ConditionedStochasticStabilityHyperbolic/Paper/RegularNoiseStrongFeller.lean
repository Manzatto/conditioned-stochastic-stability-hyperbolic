module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseSmoothing
public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedStrongFeller

/-! Strong Feller noise for the literal and fixed control cubes from the
ordinary smooth-control-density submersion source. The actual bounded
Lebesgue noise density is handled by the proved L¹ approximation argument. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory IsManifold
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Maps.strongFeller_raw_cube
    (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (smoothSource : ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      ∀ f : M → ℝ, Measurable f → (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) →
        Continuous (fun x => ∫ z : cube (ι := ι) ε,
          g z.val * f (F.family ε z.val x) ∂cubeVolume ε)) :
    RestrictedStrongFeller.HasStrongFellerNoise (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hw) := by
  intro f hf hb
  have hc := L.weighted_killed_smoothing_of_smooth_density_source ε hε
    (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
    (F.raw_measurable ε hε hw) (fun _ => (1 : ℝ)) measurable_const
    (fun _ _ => zero_le_one) 1 zero_le_one (fun _ _ => by simp)
    univ MeasurableSet.univ
    (fun g hg hs q hq hqb => by simpa only [one_mul] using smoothSource g hg hs q hq hqb)
    f hf hb
  have heq (x : M) :
      (∫ y, f y ∂WeightedRandomMapKernel.killed (L.law ε) (fun _ => (1 : ℝ))
        (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1) univ MeasurableSet.univ x) =
      ∫ y, f y ∂RandomMapKernel.transition (L.law ε)
        (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
        (F.raw_measurable ε hε hw) x := by
    rw [WeightedRandomMapKernel.integral_killed (L.law ε) (fun _ => (1 : ℝ))
      measurable_const _ (F.raw_measurable ε hε hw) (fun _ _ => zero_le_one)
      univ MeasurableSet.univ f hf,
      RandomMapKernel.integral_transition (L.law ε) _ (F.raw_measurable ε hε hw) f hf]
    simp only [one_mul, indicator_univ]
  exact hc.congr heq

omit [FiniteDimensional ℝ E] in
theorem Maps.strongFeller_fixed_cube
    (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (smoothSource : ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      ∀ f : M → ℝ, Measurable f → (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) →
        Continuous (fun x => ∫ z : cube (ι := ι) ε,
          g z.val * f (F.family ε z.val x) ∂cubeVolume ε)) :
    RestrictedStrongFeller.HasStrongFellerNoise (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2)
      (F.fixedMap_measurable ε hε hw) := by
  unfold RestrictedStrongFeller.HasStrongFellerNoise
  rw [F.transition_fixed_cube L ε hε hw]
  exact F.strongFeller_raw_cube L ε hε hw smoothSource

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
