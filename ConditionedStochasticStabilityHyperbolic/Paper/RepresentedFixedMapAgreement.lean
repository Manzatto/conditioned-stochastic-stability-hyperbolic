module

public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImageClipped
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImageRepresentation

/-! Every representation of a literal perturbation evaluates, near zero, to the fixed-control map
of the perturbation itself. Representations of the same family in different charts (for instance
a recharted carrier and the global perturbation) therefore give the same noisy map germ. -/

public noncomputable section
open Set Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι] [MetricSpace P]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} {evaluateP : P → M → M}

omit [FiniteDimensional ℝ E] in
theorem Representation.eventually_fixedMap (p : Representation F P evaluateP) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (fun z : M × FixedControl (ι := ι) => evaluateP (p.fixedParameters ε z.2) z.1) =
        (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2) := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds p.window_positive)] with ε he hp
  funext z
  exact p.actual_fixedMap ε he hp.le z.1 z.2

omit [FiniteDimensional ℝ E] in
/-- The clipped map-image letter evaluates, near zero, to the literal fixed-control map. -/
theorem MapImage.eventually_clipped_fixedMap [CompactSpace M] (hr : 1 ≤ r) (η : ℝ≥0)
    (hw : η ≤ F.window) (positive : 0 < η) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (fun z : M × FixedControl (ι := ι) => MapImage.maps F hr η hw (MapImage.clipped F hr η hw ε z.2) z.1) =
        (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2) := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds positive)] with ε he hl
  funext z
  rw [MapImage.clipped_pos F hr η hw he hl.le]
  have h1 := congrFun ((MapImage.representation F hr η hw positive).actual_map ε he hl.le
    (LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) he z.2)) z.1
  have h2 : F.fixedMap ε z.1 z.2 =
      F.family ε ((LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) he) z.2).val z.1 := by
    have he' : (0 : ℝ≥0) < ε := he
    simp only [Maps.fixedMap, he', ↓reduceDIte]
  exact h1.trans h2.symm

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
