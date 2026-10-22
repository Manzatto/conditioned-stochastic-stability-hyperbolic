module
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise

/-! Actual noise-null endpoint sets stay null after live restriction and
arbitrary bounded departure weighting. -/
public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.RestrictedNoise
open LeanShared

/-- A zero raw noise row remains zero in the literal normalized live chain. -/
theorem row_null_of_noise_null
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F)
    (K : Set X) (hK : MeasurableSet K)
    (w : K → ℝ) (hw : Measurable w)
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
    (B : Set X) (hB : MeasurableSet B) (x : K)
    (null : (ρ.map (fun a => F (x.val, a))) B = 0) :
    (chain ρ F hF K hK w hw R hR bound).killedTransition x
      (Subtype.val ⁻¹' B) = 0 := by
  have unweighted : liveKernel ρ F hF K hK x (Subtype.val ⁻¹' B) = 0 := by
    rw [liveKernel, SubtypeKernel.restrict_apply_set _ K hK x _
      (hB.preimage measurable_subtype_coe)]
    refine measure_mono_null ?_ null
    rintro y ⟨z, hz, rfl⟩
    exact hz
  rw [killedTransition]
  simp only [WeightedConditioning.normalizedKernel,
    WeightedConditioning.realWeightedKernel_apply, Measure.smul_apply,
    unweighted, smul_eq_mul, mul_zero]

end ConditionedStochasticStabilityHyperbolic.RestrictedNoise
