module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalChainGap
public import LeanShared.Probability.PositiveFunctionalMeasure

/-! # The actual leading measure constructs its complex left functional

Complex integration against the finite Riesz leading measure is bounded and
complex linear. Its compatibility with the produced real mean is proved,
rather than required alongside an independently supplied complex functional.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ComplexLeadingMeasure

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual finite measure defines a bounded complex integration functional. -/
def integralFunctional (μ : Measure X) [IsFiniteMeasure μ] : (X →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous {
    toFun := fun f => ∫ x, f x ∂μ
    map_add' := fun f g => integral_add (f.integrable μ) (g.integrable μ)
    map_smul' := fun c f => by
      simp only [BoundedContinuousFunction.smul_apply, integral_smul, RingHom.id_apply] }
    (μ.real univ) (fun f => by
      change ‖∫ x, f x ∂μ‖ ≤ μ.real univ * ‖f‖
      have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f x) (C := ‖f‖) (Filter.Eventually.of_forall f.norm_coe_le_norm)
      simpa only [mul_comm] using h)

@[simp] theorem integralFunctional_apply (μ : Measure X) [IsFiniteMeasure μ] (f : X →ᵇ ℂ) :
    integralFunctional μ f = ∫ x, f x ∂μ := rfl

/-- Representation of the real mean fixes compatibility of the constructed
complex functional on every real observable. -/
theorem integralFunctional_ofReal
    {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ) (f : X →ᵇ ℝ) :
    integralFunctional μ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (d.mean f : ℂ) := by
  rw [integralFunctional_apply, hμ]
  exact integral_complex_ofReal

/-- The normalized real pair gives the exact complex product normalization. -/
theorem integralFunctional_pair
    {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ) :
    integralFunctional μ (AbsorbingMarkovChains.ComplexKernel.ofReal d.eigenvector) = 1 := by
  rw [integralFunctional_ofReal d μ hμ, d.mean_eigenvector]
  rfl

/-- The actual complex kernel transfer commutes with real-part evaluation. -/
theorem realPart_transfer (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) (f : X →ᵇ ℂ) :
    AbsorbingMarkovChains.ComplexKernel.realPart
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF f) =
      strongFellerTransferOperator C hSF (AbsorbingMarkovChains.ComplexKernel.realPart f) := by
  let _ : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  ext x
  rw [AbsorbingMarkovChains.ComplexKernel.realPart_apply,
    ComplexStrongFeller.transferOperator_apply, strongFellerTransferOperator_represents]
  exact (integral_re (f.integrable (C.killedTransition x))).symm

theorem imagPart_transfer (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) (f : X →ᵇ ℂ) :
    AbsorbingMarkovChains.ComplexKernel.imagPart
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF f) =
      strongFellerTransferOperator C hSF (AbsorbingMarkovChains.ComplexKernel.imagPart f) := by
  let _ : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  ext x
  rw [AbsorbingMarkovChains.ComplexKernel.imagPart_apply,
    ComplexStrongFeller.transferOperator_apply, strongFellerTransferOperator_represents]
  exact (integral_im (f.integrable (C.killedTransition x))).symm

theorem integralFunctional_re
    {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ) (f : X →ᵇ ℂ) :
    (integralFunctional μ f).re = d.mean (AbsorbingMarkovChains.ComplexKernel.realPart f) := by
  rw [integralFunctional_apply, hμ]
  exact (integral_re (f.integrable μ)).symm

theorem integralFunctional_im
    {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ) (f : X →ᵇ ℂ) :
    (integralFunctional μ f).im = d.mean (AbsorbingMarkovChains.ComplexKernel.imagPart f) := by
  rw [integralFunctional_apply, hμ]
  exact (integral_im (f.integrable μ)).symm

/-- The constructed functional obeys the actual complex left eigenlaw;
no independently supplied complex law is needed. -/
theorem integralFunctional_left_law
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (d : RankOneSpectralData (strongFellerTransferOperator C hSF) (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ) (f : X →ᵇ ℂ) :
    integralFunctional μ (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF f) =
      (d.rate : ℂ) * integralFunctional μ f := by
  apply Complex.ext
  · rw [integralFunctional_re d μ hμ, realPart_transfer, d.left_eigenfunctional,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      integralFunctional_re d μ hμ]
  · rw [integralFunctional_im d μ hμ, imagPart_transfer, d.left_eigenfunctional,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      integralFunctional_im d μ hμ]

end ConditionedStochasticStabilityHyperbolic.ComplexLeadingMeasure
