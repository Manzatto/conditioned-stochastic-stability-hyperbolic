module

public import ConditionedStochasticStabilityHyperbolic.Paper.SmoothSubmersionSource
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedAllScaleMaps

/-! The actual ambient global chain is strong Feller on its original positive
noise window. Killing on an arbitrary measurable live set is handled inside
the observable, so no regularity or reference-support condition is imposed on
the absorbing boundary. The common scale window precedes every driving law. -/

public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [MetricSpace Parameters]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluate : Parameters → M → M}

omit [FiniteDimensional ℝ E] in
theorem Representation.global_strongFeller_at
    (p : Representation F Parameters evaluate) (L : Laws (ι := ι))
    (source : SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι))
    (ε : ℝ≥0) (he : 0 < ε) (window : ε ≤ p.window)
    (Live : Set M) (hLive : MeasurableSet Live)
    (w : M → ℝ) (hw : Continuous w) (nonnegative : ∀ x, 0 ≤ w x)
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R) :
    HasStrongFellerKernel (NoiseKernel.chain (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
      (p.allScale_measurable ε) Live hLive w hw.measurable R hR bound) := by
  intro f hf bounded
  obtain ⟨B, hB, hb⟩ := bounded
  have hi : Measurable (Live.indicator f) := hf.indicator hLive
  have hib : ∀ y, ‖Live.indicator f y‖ ≤ B := by
    intro y
    by_cases hy : y ∈ Live
    · simpa only [indicator_of_mem hy] using hb y
    · simpa only [indicator_of_notMem hy, norm_zero] using hB
  have cont := p.strongFeller_from_submersion L source ε he window
    (p.allScale_measurable ε) (Live.indicator f) hi ⟨B, hB, hib⟩
  have eq : (fun x => ∫ y, f y ∂(NoiseKernel.chain (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
      (p.allScale_measurable ε) Live hLive w hw.measurable R hR bound).killedTransition x) =
      (fun x => (w x / R) * ∫ y, Live.indicator f y ∂RandomMapKernel.transition
        (L.fixedLaw ε)
        (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (p.allScale_measurable ε) x) := by
    funext x
    rw [RandomMapKernel.integral_transition _ _ _ _ hi]
    exact NoiseKernel.integral_chain (L.fixedLaw ε) _ (p.allScale_measurable ε)
      Live hLive w hw.measurable nonnegative R hR bound f hf x
  rw [eq]
  exact (hw.div_const R).mul cont

omit [FiniteDimensional ℝ E] in
theorem Representation.eventually_global_strongFeller
    (p : Representation F Parameters evaluate)
    (source : SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι))
    (Live : Set M) (hLive : MeasurableSet Live)
    (w : M → ℝ) (hw : Continuous w) (nonnegative : ∀ x, 0 ≤ w x)
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ L : Laws (ι := ι),
      HasStrongFellerKernel (NoiseKernel.chain (L.fixedLaw ε)
        (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (p.allScale_measurable ε) Live hLive w hw.measurable R hR bound) := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds p.window_positive)] with ε he hw
  intro L
  exact p.global_strongFeller_at L source ε he hw.le Live hLive w ‹Continuous w› nonnegative R hR bound

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
