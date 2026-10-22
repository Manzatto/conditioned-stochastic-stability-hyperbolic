module
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalStableGapWindow
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseRegularityChange

/-! Retention refers to the same actual process probability, and is unchanged
by equal regularity labels. It is a derived conclusion, never a cited input. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
  (P : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
  (K Λ : Set M) [CompactSpace K] (hK : MeasurableSet K)
  (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)

def GapRetention : Prop :=
  ∀ ν : ℝ≥0 → ProbabilityMeasure K,
    (∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), PointAt P L K Λ hK w hw R hR bound (ν ε) ε) →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), NormalizedGapAt P L K Λ hK w hw R hR bound (ν ε) ε

/-- Relabeling regularity preserves full same-family spectral retention. -/
theorem gapRetention_changeRegularity {s : ℝ} (e : r = s) :
    GapRetention (P.changeRegularity e) L K Λ hK w hw R hR bound ↔
      GapRetention P L K Λ hK w hw R hR bound := by
  subst s
  rfl

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
