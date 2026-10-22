module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.PositiveEigenmeasure

/-! # Actual noisy-process QEM from complex complementary spectral radius

Complex and real transfers here are the actual integrals of the same killed
kernel. A strict radius bound for the complex complementary operator produces
the real exponential gap, positivity, a finite leading measure and the full
bounded-measurable quasi-ergodic property. No gap or measure is a supplied
witness. Leading spectral data and the complementary radius still have to be
obtained from the anisotropic spectral comparison.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.NoiseSpectralGap

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)

/-- Both transfers act on real tests by the same actual kernel integral. -/
theorem complexTransfer_ofReal (f : X →ᵇ ℝ) :
    ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF
      (AbsorbingMarkovChains.ComplexKernel.ofReal f) =
      AbsorbingMarkovChains.ComplexKernel.ofReal (strongFellerTransferOperator C hSF f) := by
  ext x
  rw [ComplexStrongFeller.transferOperator_apply,
    AbsorbingMarkovChains.ComplexKernel.ofReal_apply,
    strongFellerTransferOperator_represents]
  exact integral_complex_ofReal

/-- Produce the precise real rank-one data used by all conditioned-average
consumers from the complementary complex spectral-radius conclusion. -/
theorem exists_rankOne
    (r : ℝ) (hr : 0 < r) (g : X →ᵇ ℝ) (μ : (X →ᵇ ℝ) →L[ℝ] ℝ)
    (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ)
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ))
    (hpair : μ g = 1) (hmass : 0 < μ 1)
    (hright : ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
      (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hleft : ∀ f, ℓ (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF f) = (r : ℂ) * ℓ f)
    (hspec : spectralRadius ℂ (AbsorbingMarkovChains.CompactRankOneGap.remainder
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) r
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) ℓ) < ENNReal.ofReal r) :
    ∃ d : RankOneSpectralData (strongFellerTransferOperator C hSF) (1 : X →ᵇ ℝ),
      d.rate = r ∧ d.mean = μ ∧ d.eigenvector = g :=
  ComplexGap.exists_realRankOneSpectralData _ _ AbsorbingMarkovChains.ComplexKernel.ofReal
    AbsorbingMarkovChains.ComplexKernel.norm_ofReal (complexTransfer_ofReal C hSF)
    r hr g 1 μ ℓ hreal hpair hmass hright hleft hspec

variable [CompactSpace X]

/-- The actual QEM and its finite leading measure are constructed. The
geometric gap is obtained from Gelfand's formula; nonnegativity and measure
representation follow from positivity and Riesz representation. -/
theorem exists_quasiErgodic_of_complementaryRadius
    (r : ℝ) (hr : 0 < r) (g : X →ᵇ ℝ) (μ : (X →ᵇ ℝ) →L[ℝ] ℝ)
    (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ)
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ))
    (hpair : μ g = 1) (hmass : 0 < μ 1)
    (hright : ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
      (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hleft : ∀ f, ℓ (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF f) = (r : ℂ) * ℓ f)
    (hspec : spectralRadius ℂ (AbsorbingMarkovChains.CompactRankOneGap.remainder
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) r
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) ℓ) < ENNReal.ofReal r) :
    ∃ ρ : Measure X, IsFiniteMeasure ρ ∧
      (∀ f : X →ᵇ ℝ, μ f = ∫ x, f x ∂ρ) ∧
      C.IsQuasiErgodic (LeanShared.eigenvectorMeasure ρ g) := by
  obtain ⟨d, _, hdμ, hdg⟩ := exists_rankOne C hSF r hr g μ ℓ hreal hpair hmass
    hright hleft hspec
  have hpos (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
      0 ≤ strongFellerTransferOperator C hSF f x := by
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  let ρ := d.eigenmeasure hpos
  have hrep (f : X →ᵇ ℝ) : d.mean f = ∫ x, f x ∂ρ := d.eigenmeasure_represents hpos f
  refine ⟨ρ, inferInstance, ?_, ?_⟩
  · intro f
    rw [← hdμ]
    exact hrep f
  · rw [← hdg]
    exact QuasiErgodic.strongFeller_rankOne_isQuasiErgodic C hSF d ρ hrep
      (d.eigenvector_nonneg_of_positive hpos)

omit [CompactSpace X] in
/-- The manuscript's unnormalized complex spectral data construct the
corresponding raw real gap. The eigenvalue needs no probability scaling. -/
theorem exists_rawRankOne
    (R r : ℝ) (hr : 0 < r) (g : X →ᵇ ℝ) (μ : (X →ᵇ ℝ) →L[ℝ] ℝ)
    (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ)
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ))
    (hpair : μ g = 1) (hmass : 0 < μ 1)
    (hright : ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
      (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hleft : ∀ f, ℓ (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) f) =
      (r : ℂ) * ℓ f)
    (hspec : spectralRadius ℂ (AbsorbingMarkovChains.CompactRankOneGap.remainder
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) r
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) ℓ) < ENNReal.ofReal r) :
    ∃ d : RankOneSpectralData (R • strongFellerTransferOperator C hSF) (1 : X →ᵇ ℝ),
      d.rate = r ∧ d.mean = μ ∧ d.eigenvector = g := by
  apply ComplexGap.exists_realRankOneSpectralData
    (R • strongFellerTransferOperator C hSF)
    ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
    AbsorbingMarkovChains.ComplexKernel.ofReal
    AbsorbingMarkovChains.ComplexKernel.norm_ofReal _ r hr g 1 μ ℓ
    hreal hpair hmass hright hleft hspec
  intro f
  rw [smul_apply, smul_apply, complexTransfer_ofReal, map_smul]
  ext x
  simp [AbsorbingMarkovChains.ComplexKernel.ofReal_apply]

/-- Raw manuscript spectral separation yields the literal chain QEM. Weight
normalization is performed internally and preserves the actual product. -/
theorem exists_quasiErgodic_of_rawComplementaryRadius
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (g : X →ᵇ ℝ)
    (μ : (X →ᵇ ℝ) →L[ℝ] ℝ) (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ)
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ))
    (hpair : μ g = 1) (hmass : 0 < μ 1)
    (hright : ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
      (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hleft : ∀ f, ℓ (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) f) =
      (r : ℂ) * ℓ f)
    (hspec : spectralRadius ℂ (AbsorbingMarkovChains.CompactRankOneGap.remainder
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) r
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) ℓ) < ENNReal.ofReal r) :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧
      (∀ f : X →ᵇ ℝ, μ f = ∫ x, f x ∂ν) ∧
      C.IsQuasiErgodic (LeanShared.eigenvectorMeasure ν g) := by
  obtain ⟨d, _, hdμ, hdg⟩ := exists_rawRankOne C hSF R r hr g μ ℓ hreal hpair hmass
    hright hleft hspec
  have hnorm : R⁻¹ • (R • strongFellerTransferOperator C hSF) =
      strongFellerTransferOperator C hSF := by
    rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  let dn := d.ofRawNormalization R hR hnorm
  have hdnμ : dn.mean = μ := (d.ofRawNormalization_mean R hR hnorm).trans hdμ
  have hdng : dn.eigenvector = g := (d.ofRawNormalization_eigenvector R hR hnorm).trans hdg
  have hpos (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
      0 ≤ strongFellerTransferOperator C hSF f x := by
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  let ν := dn.eigenmeasure hpos
  have hrep (f : X →ᵇ ℝ) : dn.mean f = ∫ x, f x ∂ν := dn.eigenmeasure_represents hpos f
  refine ⟨ν, inferInstance, ?_, ?_⟩
  · intro f
    rw [← hdnμ]
    exact hrep f
  · rw [← hdng]
    exact QuasiErgodic.strongFeller_rankOne_isQuasiErgodic C hSF dn ν hrep
      (dn.eigenvector_nonneg_of_positive hpos)

end ConditionedStochasticStabilityHyperbolic.NoiseSpectralGap
