module

public import ConditionedStochasticStabilityHyperbolic.Paper.LocalFamilyWindow

/-! Exact transport of normalized gaps between represented fixed controls and
the literal shrinking cube, retaining the same probability family. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
/-- A chain-indexed predicate keeps exact gap transport independent of the
particular positivity proof used to represent its eigenmeasure. -/
@[expose] def NormalizedGap {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (C : AbsorbingMarkovChains.CanonicalChain X)
    (core : Set X) (ν : ProbabilityMeasure X) : Prop :=
  ∃ sf : HasStrongFellerKernel C,
  ∃ d : RankOneSpectralData (strongFellerTransferOperator C sf) (1 : X →ᵇ ℝ),
    (ν : Measure X) = eigenvectorMeasure
      (d.eigenmeasure (fun f hf x => by
        rw [strongFellerTransferOperator_represents]
        exact integral_nonneg hf)) d.eigenvector ∧
    ∀ x ∈ core, 0 < d.eigenvector x

variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [MetricSpace Parameters]
  {T : M ≃ₜ M} {r : ℝ}
  (F : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
  (K Λ : Set M) [CompactSpace K] (hK : MeasurableSet K)
  (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  {evaluate : Parameters → M → M}

/-- The full normalized power gap, exact eigenproduct, and core positivity for the probability. -/
@[expose] def NormalizedGapAt (ν : ProbabilityMeasure K) (ε : ℝ≥0) : Prop :=
  ∃ (hε : 0 < ε) (hwindow : ε ≤ F.window),
    let C := RestrictedNoise.chain (L.law ε)
      (fun z : M × RegularNoise.cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hwindow) K hK w hw R hR hwR
    NormalizedGap C {x : K | x.val ∈ Λ} ν

omit [FiniteDimensional ℝ E] [CompactSpace K] in
theorem eventual_represented_points_of_literal
    (p : RegularNoise.Representation F Parameters evaluate)
    (hmap : ∀ ε : ℝ≥0, Measurable
      (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1))
    (ν : ℝ≥0 → ProbabilityMeasure K)
    (points : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), PointAt F L K Λ hK w hw R hR hwR (ν ε) ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Point (RestrictedNoise.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (hmap ε) K hK w hw R hR hwR) R {x : K | x.val ∈ Λ} (ν ε) := by
  filter_upwards [points, p.eventually_parameters_close 1 zero_lt_one] with ε hp hε
  obtain ⟨_, _, hp⟩ := hp
  rw [← p.chain_literal_cube L ε hε.1 hε.2.1 K hK w hw R hR hwR] at hp
  exact hp

omit [FiniteDimensional ℝ E] in
theorem eventual_gaps_of_represented
    (p : RegularNoise.Representation F Parameters evaluate)
    (hmap : ∀ ε : ℝ≥0, Measurable
      (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1))
    (ν : ℝ≥0 → ProbabilityMeasure K)
    (gaps : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      let C := RestrictedNoise.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (hmap ε) K hK w hw R hR hwR
      NormalizedGap C {x : K | x.val ∈ Λ} (ν ε)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), NormalizedGapAt F L K Λ hK w hw R hR hwR (ν ε) ε := by
  filter_upwards [gaps, p.eventually_parameters_close 1 zero_lt_one] with ε hg hε
  refine ⟨hε.1, hε.2.1.trans p.window_le, ?_⟩
  rw [← p.chain_literal_cube L ε hε.1 hε.2.1 K hK w hw R hR hwR]
  exact hg

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
