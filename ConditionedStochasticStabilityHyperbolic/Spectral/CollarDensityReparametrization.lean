module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CollarDensityCertificate
public import ConditionedStochasticStabilityHyperbolic.Spectral.CollarPlaqueReparametrization
public import LeanShared.Probability.WeightedNoiseReparametrization

/-! Literal shrinking-cube inverse density data transport to fixed controls
through exact forward AND noise-weighted inverse kernel equalities. The
reference measure, transition density bound and normalization are unchanged. -/

@[expose] public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.CollarDensityCertificate
open LeanShared NoiseDensityCertificate
variable {X Ω Ξ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [TopologicalSpace Ξ] [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [BorelSpace Ω] [BorelSpace Ξ]
  {T : X ≃ₜ X} {V K G : Set X} {hK : IsCompact K}
  {ρ : Measure Ξ} [IsProbabilityMeasure ρ]
  {F : X × Ξ → X} {hF : Measurable F} {w : K → ℝ} {hw : Measurable w} {R δ : ℝ}

 def Inputs.reparametrize (c : Inputs T V K G hK ρ F hF w hw R δ) (e : Ω ≃ₜ Ξ) :
    Inputs T V K G hK (NoiseCubeRescaling.fixedLaw e ρ)
      (fun p : X × Ω => F (p.1, e p.2))
      (hF.comp (measurable_fst.prodMk (e.measurable.comp measurable_snd))) w hw R δ := by
  have hJ : ambientKernel (NoiseCubeRescaling.fixedLaw e ρ)
      (fun p : X × Ω => F (p.1, e p.2))
      (hF.comp (measurable_fst.prodMk (e.measurable.comp measurable_snd))) K hK w hw R =
      ambientKernel ρ F hF K hK w hw R := by
    unfold ambientKernel
    rw [NoiseCubeRescaling.killed_fixedLaw e ρ F hF K hK.measurableSet]
  have hL := WeightedRandomMapKernel.killed_fixedLaw e ρ c.inverseWeight c.weight_measurable
    c.inverseMap c.inverse_measurable K hK.measurableSet
  refine {
    inverseMap := fun p => c.inverseMap (p.1, e p.2)
    inverse_measurable := c.inverse_measurable.comp
      (measurable_fst.prodMk (e.measurable.comp measurable_snd))
    inverse_close := fun x hx z => c.inverse_close x hx (e z)
    inverse_plaques := c.inverse_plaques.reparametrize e
    inverseWeight := fun p => c.inverseWeight (p.1, e p.2)
    weight_measurable := c.weight_measurable.comp
      (measurable_fst.prodMk (e.measurable.comp measurable_snd))
    weightBound := c.weightBound
    weight_bounded := fun x z => c.weight_bounded x (e z)
    weight_positive := fun x hx hg z => c.weight_positive x hx hg (e z)
    reference := c.reference
    reference_finite := c.reference_finite
    reference_support := c.reference_support
    transitionDensity := c.transitionDensity
    transition_measurable := c.transition_measurable
    densityBound := c.densityBound
    densityBound_finite := c.densityBound_finite
    transition_bounded := c.transition_bounded
    transition_representation := ?_
    duality := ?_
    inverse_smoothing := ?_ }
  · intro x
    rw [hJ]
    exact c.transition_representation x
  · rw [hJ, hL]
    exact c.duality
  · intro f hf hb
    simpa only [hL] using c.inverse_smoothing f hf hb

end ConditionedStochasticStabilityHyperbolic.CollarDensityCertificate
