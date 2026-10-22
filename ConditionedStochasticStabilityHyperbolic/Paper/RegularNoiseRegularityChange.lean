module
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions

/-! Equal regularity labels change none of the actual maps, controls, laws,
chains or local conclusions. This only aligns product and auxiliary labels. -/
public noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r s : ℝ}

@[expose] def Maps.changeRegularity (P : Maps (E := E) (ι := ι) T r) (e : r = s) :
    Maps (E := E) (ι := ι) T s := e ▸ P

theorem Maps.changeRegularity_family (P : Maps (E := E) (ι := ι) T r)
    (e : r = s) (ε : ℝ≥0) (a : Control (ι := ι)) (x : M) :
    (P.changeRegularity e).family ε a x = P.family ε a x := by
  subst s
  rfl

theorem Maps.changeRegularity_window (P : Maps (E := E) (ι := ι) T r) (e : r = s) :
    (P.changeRegularity e).window = P.window := by
  subst s
  rfl

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [CompactSpace M] in
theorem Maps.stability_changeRegularity
    (P : Maps (E := E) (ι := ι) T r) (e : r = s) (L : Laws (ι := ι))
    (K Λ : Set M) [CompactSpace K] (hK : MeasurableSet K)
    (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) (potential : M → ℝ) :
    LocalConclusions.Stability (P.changeRegularity e) L K Λ hK w hw R hR hwR potential ↔
      LocalConclusions.Stability P L K Λ hK w hw R hR hwR potential := by
  subst s
  rfl

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
