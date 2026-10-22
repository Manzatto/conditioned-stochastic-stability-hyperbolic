module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexLeadingMeasure

/-! # Actual complex power convergence from the produced real gap

Real and imaginary parts use the same actual killed kernel. The real gap and
its represented finite measure therefore determine the complex rank-one
power limit on every observable; no extra complex spectral-gap premise is
needed in invariant common-core approximation.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ComplexPowerConvergence

open AbsorbingMarkovChains.ComplexKernel

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem tendsto_normalized_apply_of_intertwining
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (Q : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ))
    (hcomm : ∀ f, Q (ofReal f) = ofReal (P f))
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ) (f : X →ᵇ ℂ) :
    Tendsto (fun n : ℕ => (((d.rate : ℂ)⁻¹ •
      Q) ^ n) f) atTop
      (𝓝 (ComplexLeadingMeasure.integralFunctional μ f • ofReal d.eigenvector)) := by
  let R := fun n : ℕ => (d.normalizedOperator ^ n) (AbsorbingMarkovChains.ComplexKernel.realPart f)
  let I := fun n : ℕ => (d.normalizedOperator ^ n) (imagPart f)
  have hR : Tendsto R atTop (𝓝 (d.mean (AbsorbingMarkovChains.ComplexKernel.realPart f) • d.eigenvector)) := by
    simpa only [R, Function.comp_def, ContinuousLinearMap.apply_apply, RankOneSpectralData.projection, ContinuousLinearMap.smulRight_apply] using
      (ContinuousLinearMap.apply ℝ (X →ᵇ ℝ) (AbsorbingMarkovChains.ComplexKernel.realPart f)).continuous.continuousAt.tendsto.comp
        d.tendsto_powers
  have hI : Tendsto I atTop (𝓝 (d.mean (imagPart f) • d.eigenvector)) := by
    simpa only [I, Function.comp_def, ContinuousLinearMap.apply_apply, RankOneSpectralData.projection, ContinuousLinearMap.smulRight_apply] using
      (ContinuousLinearMap.apply ℝ (X →ᵇ ℝ) (imagPart f)).continuous.continuousAt.tendsto.comp
        d.tendsto_powers
  have hr := ofReal.continuous.continuousAt.tendsto.comp hR
  have hi := (ofReal.continuous.continuousAt.tendsto.comp hI).const_smul Complex.I
  have hsum := hr.add hi
  have hvalue : ofReal (d.mean (AbsorbingMarkovChains.ComplexKernel.realPart f) • d.eigenvector) +
      Complex.I • ofReal (d.mean (imagPart f) • d.eigenvector) =
      ComplexLeadingMeasure.integralFunctional μ f • ofReal d.eigenvector := by
    ext x
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
      ofReal_apply, smul_eq_mul, Complex.ofReal_mul]
    rw [← ComplexLeadingMeasure.integralFunctional_re d μ hμ f,
      ← ComplexLeadingMeasure.integralFunctional_im d μ hμ f]
    rw [← mul_assoc, ← add_mul, mul_comm Complex.I, Complex.re_add_im]
  rw [hvalue] at hsum
  apply hsum.congr'
  exact Eventually.of_forall (fun n => by
    have hdecomp : f = ofReal (AbsorbingMarkovChains.ComplexKernel.realPart f) + Complex.I • ofReal (imagPart f) := by
      ext x
      simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
        ofReal_apply, realPart_apply, imagPart_apply, smul_eq_mul]
      rw [mul_comm Complex.I]
      exact (Complex.re_add_im (f x)).symm
    have hrn := ComplexGap.normalized_power_intertwines
      P Q
      ofReal hcomm d.rate n (AbsorbingMarkovChains.ComplexKernel.realPart f)
    have hin := ComplexGap.normalized_power_intertwines
      P Q
      ofReal hcomm d.rate n (imagPart f)
    change ofReal (R n) + Complex.I • ofReal (I n) =
      (((d.rate : ℂ)⁻¹ • Q) ^ n) f
    rw [hdecomp, map_add, map_smul, hrn, hin]
    rfl)


theorem tendsto_normalized_apply
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (d : RankOneSpectralData (strongFellerTransferOperator C hSF) (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ) (f : X →ᵇ ℂ) :
    Tendsto (fun n : ℕ => (((d.rate : ℂ)⁻¹ •
      ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) ^ n) f) atTop
      (𝓝 (ComplexLeadingMeasure.integralFunctional μ f • ofReal d.eigenvector)) := by
  let R := fun n : ℕ => (d.normalizedOperator ^ n) (AbsorbingMarkovChains.ComplexKernel.realPart f)
  let I := fun n : ℕ => (d.normalizedOperator ^ n) (imagPart f)
  have hR : Tendsto R atTop (𝓝 (d.mean (AbsorbingMarkovChains.ComplexKernel.realPart f) • d.eigenvector)) := by
    simpa only [R, Function.comp_def, ContinuousLinearMap.apply_apply, RankOneSpectralData.projection, ContinuousLinearMap.smulRight_apply] using
      (ContinuousLinearMap.apply ℝ (X →ᵇ ℝ) (AbsorbingMarkovChains.ComplexKernel.realPart f)).continuous.continuousAt.tendsto.comp
        d.tendsto_powers
  have hI : Tendsto I atTop (𝓝 (d.mean (imagPart f) • d.eigenvector)) := by
    simpa only [I, Function.comp_def, ContinuousLinearMap.apply_apply, RankOneSpectralData.projection, ContinuousLinearMap.smulRight_apply] using
      (ContinuousLinearMap.apply ℝ (X →ᵇ ℝ) (imagPart f)).continuous.continuousAt.tendsto.comp
        d.tendsto_powers
  have hr := ofReal.continuous.continuousAt.tendsto.comp hR
  have hi := (ofReal.continuous.continuousAt.tendsto.comp hI).const_smul Complex.I
  have hsum := hr.add hi
  have hvalue : ofReal (d.mean (AbsorbingMarkovChains.ComplexKernel.realPart f) • d.eigenvector) +
      Complex.I • ofReal (d.mean (imagPart f) • d.eigenvector) =
      ComplexLeadingMeasure.integralFunctional μ f • ofReal d.eigenvector := by
    ext x
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
      ofReal_apply, smul_eq_mul, Complex.ofReal_mul]
    rw [← ComplexLeadingMeasure.integralFunctional_re d μ hμ f,
      ← ComplexLeadingMeasure.integralFunctional_im d μ hμ f]
    rw [← mul_assoc, ← add_mul, mul_comm Complex.I, Complex.re_add_im]
  rw [hvalue] at hsum
  apply hsum.congr'
  exact Eventually.of_forall (fun n => by
    have hdecomp : f = ofReal (AbsorbingMarkovChains.ComplexKernel.realPart f) + Complex.I • ofReal (imagPart f) := by
      ext x
      simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
        ofReal_apply, realPart_apply, imagPart_apply, smul_eq_mul]
      rw [mul_comm Complex.I]
      exact (Complex.re_add_im (f x)).symm
    have hcomm := NoiseSpectralGap.complexTransfer_ofReal C hSF
    have hrn := ComplexGap.normalized_power_intertwines
      (strongFellerTransferOperator C hSF) (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
      ofReal hcomm d.rate n (AbsorbingMarkovChains.ComplexKernel.realPart f)
    have hin := ComplexGap.normalized_power_intertwines
      (strongFellerTransferOperator C hSF) (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
      ofReal hcomm d.rate n (imagPart f)
    change ofReal (R n) + Complex.I • ofReal (I n) =
      (((d.rate : ℂ)⁻¹ • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) ^ n) f
    rw [hdecomp, map_add, map_smul, hrn, hin]
    rfl)

end ConditionedStochasticStabilityHyperbolic.ComplexPowerConvergence
