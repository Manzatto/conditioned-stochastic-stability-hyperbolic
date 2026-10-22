module

public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedAllScaleMaps

/-! Different anisotropic charts may represent one literal perturbation in
different parameter spaces. They still produce exactly the same global chain
near zero, before any driving law is chosen. -/

public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [MetricSpace P] [MetricSpace Q]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluateP : P → M → M} {evaluateQ : Q → M → M}

omit [FiniteDimensional ℝ E] [MeasurableSpace M] [BorelSpace M] in
theorem Representation.eventually_same_maps
    (p : Representation F P evaluateP) (q : Representation F Q evaluateQ) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (fun z : M × FixedControl (ι := ι) => evaluateP (p.fixedParameters ε z.2) z.1) =
        (fun z : M × FixedControl (ι := ι) => evaluateQ (q.fixedParameters ε z.2) z.1) := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds p.window_positive),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds q.window_positive)] with ε he hp hq
  funext z
  exact (p.actual_fixedMap ε he hp.le z.1 z.2).trans
    (q.actual_fixedMap ε he hq.le z.1 z.2).symm

omit [FiniteDimensional ℝ E] in
theorem Representation.eventually_same_global_chain
    (p : Representation F P evaluateP) (q : Representation F Q evaluateQ)
    (Live : Set M) (hLive : MeasurableSet Live) (w : M → ℝ) (hw : Measurable w)
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ L : Laws (ι := ι),
      NoiseKernel.chain (L.fixedLaw ε)
        (fun z : M × FixedControl (ι := ι) => evaluateP (p.fixedParameters ε z.2) z.1)
        (p.allScale_measurable ε) Live hLive w hw R hR bound =
      NoiseKernel.chain (L.fixedLaw ε)
        (fun z : M × FixedControl (ι := ι) => evaluateQ (q.fixedParameters ε z.2) z.1)
        (q.allScale_measurable ε) Live hLive w hw R hR bound := by
  filter_upwards [p.eventually_same_maps q] with ε eq
  intro L
  congr 1

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
