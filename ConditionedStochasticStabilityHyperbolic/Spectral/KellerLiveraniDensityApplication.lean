module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniRetainedApplication
public import ConditionedStochasticStabilityHyperbolic.Spectral.DensityStrongFeller

/-! # Retained KL spectral gap with actual density compactness

The physical continuous operator's compactness is produced from the classical
noise density, rather than supplied independently. Retained-region comparison
and canonical positivity orientation then construct the actual raw real gap.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

theorem ProjectorOutputs.exists_canonicalRawGap_of_actual_density
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) (scale : ℝ) (hscale : 0 < scale)
    (C : AbsorbingMarkovChains.CanonicalChain Y) (hSF : HasStrongFellerKernel C)
    (R : ℝ) (hR : 0 < R)
    (a : E →L[ℂ] Z) (b : (Y →ᵇ ℂ) →L[ℂ] Z)
    (σ : Measure Y) [IsFiniteMeasure σ]
    (k : Y × Y → ℝ) (hk : Measurable k) (hk0 : ∀ x y, 0 ≤ k (x, y))
    (hkernel : ∀ x, C.killedTransition x =
      σ.withDensity (fun y => ENNReal.ofReal (k (x, y))))
    (M : ℝ) (hM : 0 ≤ M) (hkM : ∀ x y, ‖k (x, y)‖ ≤ M)
    (hcontinuous : ∀ᵐ y ∂σ, Continuous (fun x => k (x, y)))
    (hcompare : ComparedSpectralGap.EigenvectorComparison ((scale : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) a b (scale * q))
    (hsep : RestrictedSpectralComparison.SeparatesEigenspace
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) b
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ))
    (g : Y →ᵇ ℝ) (μ : (Y →ᵇ ℝ) →L[ℝ] ℝ) (ℓ : (Y →ᵇ ℂ) →L[ℂ] ℂ)
    (hident : b (AbsorbingMarkovChains.ComplexKernel.ofReal g) = a (o.vector ε))
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ))
    (hpair : μ g = 1)
    (hright : ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hleft : ∀ f, ℓ (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) f) =
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ) * ℓ f) :
    μ 1 ≠ 0 ∧ ∃ dc : RankOneSpectralData
      (R • strongFellerTransferOperator C hSF) (1 : Y →ᵇ ℝ),
      dc.rate = scale * (o.eigenvalue ε).re ∧ dc.mean 1 = 1 ∧
      dc.mean = (μ 1)⁻¹ • μ ∧ dc.eigenvector = μ 1 • g := by
  have hp := DensityStrongFeller.compact_complex_transfer_of_density
    C hSF σ k hk hk0 hkernel M hM hkM hcontinuous
  have hcompact : IsCompactOperator
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) := hp.smul (R : ℂ)
  let Q := (R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF
  let rawP := R • strongFellerTransferOperator C hSF
  let r := scale * (o.eigenvalue ε).re
  have hr : 0 < r := mul_pos hscale (hq.trans (o.eigenvalue_re_gt hδlead ε hε))
  have hpairC : ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal g) = 1 := by
    rw [hreal, hpair]
    rfl
  have hgC : AbsorbingMarkovChains.ComplexKernel.ofReal g ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hpairC
    exact zero_ne_one hpairC
  let : Nontrivial (Y →ᵇ ℂ) := ⟨⟨AbsorbingMarkovChains.ComplexKernel.ofReal g, 0, hgC⟩⟩
  have hspec := RestrictedSpectralComparison.complementary_radius_lt_of_compact
    ((scale : ℂ) • P ε) Q a b (scale * q) r
    (mul_lt_mul_of_pos_left (o.eigenvalue_re_gt hδlead ε hε) hscale) hr
    hcompare hsep hcompact (o.vector ε)
    (AbsorbingMarkovChains.ComplexKernel.ofReal g) hident ℓ hpairC hright hleft
    (o.raw_eigenvalue_bound hδsub hδlead hq ε hε c scale hscale)
    (o.raw_peripheral_exclusion hδsub hδlead hq ε hε c scale hscale)
    (o.raw_leading_simple hδsub hδlead ε hε c scale hscale)
  have hcomm (f : Y →ᵇ ℝ) : Q (AbsorbingMarkovChains.ComplexKernel.ofReal f) =
      AbsorbingMarkovChains.ComplexKernel.ofReal (rawP f) := by
    rw [show Q = (R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF from rfl,
      smul_apply, NoiseSpectralGap.complexTransfer_ofReal]
    change (R : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal (strongFellerTransferOperator C hSF f) =
      AbsorbingMarkovChains.ComplexKernel.ofReal (R • strongFellerTransferOperator C hSF f)
    ext x
    simp [AbsorbingMarkovChains.ComplexKernel.ofReal_apply]
  have hpositive (f : Y →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : Y) : 0 ≤ rawP f x := by
    change 0 ≤ R * strongFellerTransferOperator C hSF f x
    rw [strongFellerTransferOperator_represents]
    exact mul_nonneg hR.le (integral_nonneg hf)
  obtain ⟨hα, dc, hdcRate, hdcMean, hdcVector, hdcOne, _⟩ :=
    ProjectorOrientation.exists_canonicalRankOne_of_complexRadius rawP r hr g μ Q hcomm
      hpositive ℓ hreal hpair hright hleft hspec
  exact ⟨hα, dc, hdcRate, hdcOne, hdcMean, hdcVector⟩

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
