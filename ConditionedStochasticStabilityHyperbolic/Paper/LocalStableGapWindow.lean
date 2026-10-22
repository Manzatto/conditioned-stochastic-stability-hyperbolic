module

public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapFamilyWindow

/-! Constructive assembly of a stable family and its retained actual gaps.
The probability family is unchanged; only its positive window is shrunk. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
  (N : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
  (K Λ : Set M) [CompactSpace K] (hK : MeasurableSet K)
  (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (potential : M → ℝ)

/-- Both assumptions are proved outputs in the actual source application.
In particular the retention function is not a classical/noisy source field. -/
theorem stable_gap_window
    (stability : Stability N L K Λ hK w hw R hR hwR potential)
    (retain : ∀ ν : ℝ≥0 → ProbabilityMeasure K,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), PointAt N L K Λ hK w hw R hR hwR (ν ε) ε) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), NormalizedGapAt N L K Λ hK w hw R hR hwR (ν ε) ε) :
  ∃ (ν₀ : ProbabilityMeasure K) (νeq : ProbabilityMeasure M),
    (ν₀ : Measure K).map Subtype.val = (νeq : Measure M) ∧
    ThermodynamicDefinitions.IsEquilibriumState T
      potential Λ νeq ∧
    (∀ ζ : ProbabilityMeasure M, ThermodynamicDefinitions.IsEquilibriumState T
      potential Λ ζ → ζ = νeq) ∧
    ∃ (δ : ℝ≥0) (hwindow : δ ≤ N.window), 0 < δ ∧
    ∃ ν : ℝ≥0 → ProbabilityMeasure K,
      Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) ∧
      (∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
        LocalConclusions.Point (RestrictedNoise.chain (L.law ε)
          (fun z : M × RegularNoise.cube (ι := ι) ε => N.family ε z.2.val z.1)
          (N.raw_measurable ε hε (hεδ.trans hwindow)) K hK w
          hw R hR hwR) R {x | x.val ∈ Λ} (ν ε)) ∧
      ∀ ε (_hε : 0 < ε) (_hεδ : ε ≤ δ), LocalConclusions.NormalizedGapAt N L K Λ
        hK w hw R hR hwR (ν ε) ε := by
  obtain ⟨ν₀, νeq, hmap, heq, huniq, δ, hwindow, hδ, ν, limit, points⟩ := stability
  have pointsAt : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      LocalConclusions.PointAt N L K Λ hK w hw
        R hR hwR (ν ε) ε := by
    have window : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), 0 < ε ∧ ε ≤ δ := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε hεδ
      exact ⟨hε, hεδ.le⟩
    filter_upwards [window] with ε hε
    exact ⟨hε.1, hε.2.trans hwindow, points ε hε.1 hε.2⟩
  have gaps := retain ν pointsAt
  obtain ⟨δg, hδg, hg⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp gaps
  refine ⟨ν₀, νeq, hmap, heq, huniq, min δ δg,
    (min_le_left _ _).trans hwindow, lt_min hδ hδg, ν, limit, ?_, ?_⟩
  · intro ε hε hεδ
    exact points ε hε (hεδ.trans (min_le_left _ _))
  · intro ε hε hεδ
    exact hg ⟨hε, hεδ.trans (min_le_right _ _)⟩


end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
