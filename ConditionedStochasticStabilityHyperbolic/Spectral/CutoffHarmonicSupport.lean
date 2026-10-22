module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveEigenfunction

/-! Actual harmonic vectors vanish at zero departure weights. The cutoff
weight's compact interior support therefore supplies the supported smooth
core approximation needed for physical projector comparison. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.CutoffHarmonicSupport

open LeanShared LeanShared.WeightedConditioning LocalPositiveEigenfunction

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω]

theorem tsupport_eigenvector_subset_weight
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
    (K : Set X) (hK : MeasurableSet K) (w : K → ℝ) (hw : Measurable w)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hSF : HasStrongFellerKernel (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR))
    (d : RankOneSpectralData (strongFellerTransferOperator
      (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR) hSF) (1 : K →ᵇ ℝ)) :
    tsupport (AbsorbingMarkovChains.ComplexKernel.ofReal d.eigenvector) ⊆ tsupport w := by
  apply closure_mono
  intro x hx
  change w x ≠ 0
  intro hwzero
  let C := RestrictedNoise.chain ρ F hF K hK w hw R hR hwR
  have hh (y : K) : ∫ z, d.eigenvector z ∂C.killedTransition y = d.rate * d.eigenvector y := by
    rw [← strongFellerTransferOperator_represents C hSF]
    simpa only [BoundedContinuousFunction.smul_apply, smul_eq_mul] using
      congrArg (fun f : K →ᵇ ℝ => f y) d.right_eigenvector
  have ha := ambient_right_law ρ F hF K hK w hw R hR hwR
    d.eigenvector d.rate hh x
  have hwa : SubtypeKernel.zeroExtend K w x.val = 0 := by
    rw [SubtypeKernel.zeroExtend_coe, hwzero]
  change (∫ y, SubtypeKernel.zeroExtend K d.eigenvector y ∂
    (ENNReal.ofReal (SubtypeKernel.zeroExtend K w x.val / R) •
      LeanShared.RandomMapKernel.killed ρ F hF K hK x.val)) = _ at ha
  rw [hwa, zero_div, ENNReal.ofReal_zero, zero_smul, integral_zero_measure] at ha
  have hgx : d.eigenvector x = 0 := (mul_eq_zero.mp ha.symm).resolve_left (ne_of_gt d.rate_pos)
  exact hx (by simp only [AbsorbingMarkovChains.ComplexKernel.ofReal_apply, hgx, Complex.ofReal_zero])

end ConditionedStochasticStabilityHyperbolic.CutoffHarmonicSupport
