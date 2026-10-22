module

public import ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedCubeChains
public import ConditionedStochasticStabilityHyperbolic.Paper.NoiseSmallness
public import Mathlib.Topology.Order.LeftRightNhds

/-! Eventual local conclusions give one explicit positive noise window before
all states and observables. The weakly convergent family remains unchanged,
and represented map-space chains transfer to the literal shrinking cube. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
  (F : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
  (K Λ : Set M) [CompactSpace K] (hK : MeasurableSet K)
  (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)

/-- Only positive noise sizes inside the ordinary perturbation window enter
this pointwise predicate; all chain measurability proofs are constructed. -/
def PointAt (ν : ProbabilityMeasure K) (ε : ℝ≥0) : Prop :=
  ∃ (hε : 0 < ε) (hwindow : ε ≤ F.window),
    Point (RestrictedNoise.chain (L.law ε)
      (fun z : M × RegularNoise.cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hwindow) K hK w hw R hR hwR)
      R {x : K | x.val ∈ Λ} ν

omit [FiniteDimensional ℝ E] [CompactSpace K] in
theorem exists_window_of_eventual_points (ν : ℝ≥0 → ProbabilityMeasure K)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), PointAt F L K Λ hK w hw R hR hwR (ν ε) ε) :
    ∃ (δ : ℝ≥0) (hwindow : δ ≤ F.window), 0 < δ ∧
      ∀ ε : ℝ≥0, (hε : 0 < ε) → (hδ : ε ≤ δ) →
        Point (RestrictedNoise.chain (L.law ε)
          (fun z : M × RegularNoise.cube (ι := ι) ε => F.family ε z.2.val z.1)
          (F.raw_measurable ε hε (hδ.trans hwindow)) K hK w hw R hR hwR)
          R {x : K | x.val ∈ Λ} (ν ε) := by
  obtain ⟨δ, hδ, hp⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp h
  obtain ⟨_he, hwindow, _point⟩ := hp ⟨hδ, le_rfl⟩
  refine ⟨δ, hwindow, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨_he, _hw, point⟩ := hp ⟨hε, hεδ⟩
  exact point

omit [FiniteDimensional ℝ E] [CompactSpace K] in
theorem existence_of_eventual_points (ν : ℝ≥0 → ProbabilityMeasure K)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), PointAt F L K Λ hK w hw R hR hwR (ν ε) ε) :
    Existence F L K Λ hK w hw R hR hwR := by
  obtain ⟨δ, hwindow, hδ, hp⟩ := exists_window_of_eventual_points F L K Λ hK w hw R hR hwR ν h
  exact ⟨δ, hwindow, hδ, ν, hp⟩

omit [FiniteDimensional ℝ E] [CompactSpace K] in
theorem stability_of_eventual_points (potential : M → ℝ)
    (ν₀ : ProbabilityMeasure K) (νeq : ProbabilityMeasure M)
    (map_eq : (ν₀ : Measure K).map Subtype.val = (νeq : Measure M))
    (equilibrium : ThermodynamicDefinitions.IsEquilibriumState T potential Λ νeq)
    (unique : ∀ ζ : ProbabilityMeasure M,
      ThermodynamicDefinitions.IsEquilibriumState T potential Λ ζ → ζ = νeq)
    (ν : ℝ≥0 → ProbabilityMeasure K) (limit : Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀))
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), PointAt F L K Λ hK w hw R hR hwR (ν ε) ε) :
    Stability F L K Λ hK w hw R hR hwR potential := by
  obtain ⟨δ, hwindow, hδ, hp⟩ := exists_window_of_eventual_points F L K Λ hK w hw R hR hwR ν h
  exact ⟨ν₀, νeq, map_eq, equilibrium, unique, δ, hwindow, hδ, ν, limit, hp⟩

variable {Parameters : Type*} [MetricSpace Parameters] {evaluate : Parameters → M → M}

omit [FiniteDimensional ℝ E] [CompactSpace K] in
theorem eventual_points_of_represented
    (p : RegularNoise.Representation F Parameters evaluate)
    (hmap : ∀ ε : ℝ≥0, Measurable
      (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1))
    (ν : ℝ≥0 → ProbabilityMeasure K)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Point (RestrictedNoise.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (hmap ε) K hK w hw R hR hwR) R {x : K | x.val ∈ Λ} (ν ε)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), PointAt F L K Λ hK w hw R hR hwR (ν ε) ε := by
  filter_upwards [h, p.eventually_parameters_close 1 zero_lt_one] with ε hp hε
  refine ⟨hε.1, hε.2.1.trans p.window_le, ?_⟩
  rw [← p.chain_literal_cube L ε hε.1 hε.2.1 K hK w hw R hR hwR]
  exact hp

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
