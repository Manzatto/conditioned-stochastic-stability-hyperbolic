module
public import LeanShared.MeasureTheory.CoordinateMeasureRecovery
public import LeanShared.MeasureTheory.WeightedPushforward
public import Mathlib.Tactic.FieldSimp

/-! The quotient of actual local coordinate densities is the genuine local
Radon--Nikodym factor on the manifold. -/
public noncomputable section
namespace LeanShared.CoordinateDensityRatio
open Set MeasureTheory Measure
open scoped ENNReal

theorem local_law
    {E M : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (c : OpenPartialHomeomorph M E) (μ : Measure E) (σ ν : Measure M)
    (p q : E → ℝ) (measurableP : Measurable p) (measurableQ : Measurable q)
    (positiveP : ∀ y ∈ c.target, 0 < p y)
    (lawP : (σ.restrict c.source).map c = (μ.restrict c.target).withDensity (fun y => ENNReal.ofReal (p y)))
    (lawQ : (ν.restrict c.source).map c = (μ.restrict c.target).withDensity (fun y => ENNReal.ofReal (q y))) :
    ν.restrict c.source = (σ.restrict c.source).withDensity (fun x => ENNReal.ofReal (q (c x) / p (c x))) := by
  let r : E → ℝ≥0∞ := fun y => ENNReal.ofReal (q y / p y)
  have measurableR : Measurable r := (measurableQ.div measurableP).ennreal_ofReal
  have supported : ∀ᵐ x ∂σ.restrict c.source, x ∈ c.source := ae_restrict_mem c.open_source.measurableSet
  have weightedSupport : ∀ᵐ x ∂(σ.restrict c.source).withDensity (r ∘ c), x ∈ c.source :=
    (withDensity_absolutelyContinuous _ _).ae_le supported
  apply CoordinateMeasureRecovery.injective c _ _ (ae_restrict_mem c.open_source.measurableSet) weightedSupport
  rw [lawQ,WeightedPushforward.map_withDensity_comp _
    (c.continuousOn.aemeasurable c.open_source.measurableSet) measurableR,lawP,
    ←withDensity_mul _ measurableP.ennreal_ofReal measurableR]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem c.open_target.measurableSet] with y hy
  change ENNReal.ofReal (q y) = ENNReal.ofReal (p y) * ENNReal.ofReal (q y / p y)
  rw [←ENNReal.ofReal_mul (positiveP y hy).le]
  congr 1
  field_simp [(positiveP y hy).ne']

end LeanShared.CoordinateDensityRatio
