module

public import ConditionedStochasticStabilityHyperbolic.Paper.InverseDensityFamily

/-! The law-independent ordinary inverse source supplies the eventual density
field of the literal represented layer. Its small-noise threshold is common
to every admissible family of driving laws. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared ControlledPlaqueClosure
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MetricSpace Parameters]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluate : Parameters → M → M} {σ : Measure M} {V K G : Set M} {w : K → ℝ} {R : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Representation.eventually_inverse_density_inputs
    (p : Representation F Parameters evaluate)
    (d : InverseDensityOrdinarySources F σ V K G w R)
    [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (hK : IsCompact K) (hV : IsOpen V) (hG : IsOpen G) (hVK : V ⊆ K)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (hwt : Measurable w) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hF : ∀ ε, Measurable (fun z : M × FixedControl (ι := ι) =>
      evaluate (p.fixedParameters ε z.2) z.1))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ∀ L : Laws (ι := ι),
      Nonempty (Global.NoFullSupportCollarDensityCertificate.Inputs T V K G hK (L.fixedLaw ε)
        (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (hF ε) w hwt R η) := by
  have hp : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ε < p.window :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds p.window_positive)
  filter_upwards [d.eventually_fixed_inputs source hK hV hG hVK hcoreV hcoreG hwt hR hwR η hη,
    self_mem_nhdsWithin, hp] with ε hd he hp L
  obtain ⟨c⟩ := hd L he (hp.le.trans p.window_le)
  exact ⟨p.represented_density_inputs L ε he hp.le V K G hK w hwt R η c (hF ε)⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
