module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise

/-! The actual complex weighted noise integral, including boundary killing.
It connects the literal finite-regular weighted composition to the physical
strong-Feller transfer, without a deterministic C0 transfer operator. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace ConditionedStochasticStabilityHyperbolic.RestrictedNoise

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

theorem integral_chain_complex
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
    (K : Set X) (hK : MeasurableSet K) (w : K → ℝ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (f : K → ℂ) (hf : Measurable f) (x : K) :
    (∫ y, f y ∂(chain ρ F hF K hK w hw R hR hwR).killedTransition x) =
      (w x / R) • ∫ ω, ComplexStrongFeller.zeroExtend K f (F (x.val, ω)) ∂ρ := by
  rw [killedTransition]
  change (∫ y, f y ∂(ENNReal.ofReal (w x / R) • liveKernel ρ F hF K hK x)) = _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (div_nonneg (hw0 x) hR.le)]
  congr 1
  have hs := integral_subtype_comap hK (ComplexStrongFeller.zeroExtend K f)
    (μ := LeanShared.RandomMapKernel.transition ρ F hF x.val)
  simp only [ComplexStrongFeller.zeroExtend_coe] at hs
  change (∫ y, f y ∂Measure.comap Subtype.val
    (LeanShared.RandomMapKernel.transition ρ F hF x.val)) = _
  rw [hs, ← integral_indicator hK]
  have hind : K.indicator (ComplexStrongFeller.zeroExtend K f) =
      ComplexStrongFeller.zeroExtend K f := by
    funext y
    by_cases hy : y ∈ K
    · simp only [Set.indicator_of_mem hy]
    · simp only [Set.indicator_of_notMem hy,
        ComplexStrongFeller.zeroExtend_of_not_mem K f y hy]
  rw [hind]
  exact integral_map_of_stronglyMeasurable (hF.comp measurable_prodMk_left)
    (ComplexStrongFeller.measurable_zeroExtend K hK f hf).stronglyMeasurable

end ConditionedStochasticStabilityHyperbolic.RestrictedNoise
