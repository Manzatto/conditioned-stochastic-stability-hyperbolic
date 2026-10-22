module
public import LeanShared.MeasureTheory.CoordinatePatchMeasure

/-! Measures supported in an actual chart are recovered exactly from their
coordinate pushforward. No globally measurable chart extension is assumed. -/
public noncomputable section
namespace LeanShared.CoordinateMeasureRecovery
open Set MeasureTheory Measure

theorem recover
    {E M : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (c : OpenPartialHomeomorph M E) (ν : Measure M)
    (support : ∀ᵐ x ∂ν, x ∈ c.source) : (ν.map c).map c.symm = ν := by
  have restrict : ν.restrict c.source = ν := Measure.restrict_eq_self_of_ae_mem support
  have measurable : AEMeasurable c ν := by
    rw [←restrict]
    exact c.continuousOn.aemeasurable c.open_source.measurableSet
  have target : ∀ᵐ y ∂ν.map c, y ∈ c.target := by
    apply (ae_map_iff measurable c.open_target.measurableSet).mpr
    exact support.mono (fun x hx => c.map_source hx)
  have inverseMeasurable : AEMeasurable c.symm (ν.map c) := by
    rw [←Measure.restrict_eq_self_of_ae_mem target]
    exact c.symm.continuousOn.aemeasurable c.open_target.measurableSet
  rw [AEMeasurable.map_map_of_aemeasurable inverseMeasurable measurable]
  have same : c.symm ∘ c =ᵐ[ν] id := support.mono (fun x hx => c.left_inv hx)
  rw [Measure.map_congr same,Measure.map_id]

theorem injective
    {E M : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (c : OpenPartialHomeomorph M E) (μ ν : Measure M)
    (supportμ : ∀ᵐ x ∂μ, x ∈ c.source) (supportν : ∀ᵐ x ∂ν, x ∈ c.source)
    (same : μ.map c = ν.map c) : μ = ν := by
  rw [←recover c μ supportμ,←recover c ν supportν,same]

end LeanShared.CoordinateMeasureRecovery
