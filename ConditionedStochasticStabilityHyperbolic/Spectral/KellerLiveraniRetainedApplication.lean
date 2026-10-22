module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniCanonicalApplication
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedSpectralComparison

/-! # Canonical actual gap through retained-region spectral comparison

Unlike the global-embedding interface, restriction here needs to separate
only the leading eigenspace. The geometric nonreturn/extinction producers
establish that separation. Analytic and physical eigenfunctions are matched
on the retained region; equality away from that region is unnecessary.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

/-- KL outputs and geometric retained-region separation produce the actual
raw real rank-one gap. Its orientation and positive left mass are derived.
The maps into `Z` may be restrictions and need not be globally injective. -/
theorem ProjectorOutputs.exists_canonicalRawGap_of_retained_comparison
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) (scale : ℝ) (hscale : 0 < scale)
    (C : AbsorbingMarkovChains.CanonicalChain Y) (hSF : HasStrongFellerKernel C)
    (R : ℝ) (hR : 0 < R)
    (a : E →L[ℂ] Z) (b : (Y →ᵇ ℂ) →L[ℂ] Z)
    (hFredholm : PowerCompactGap.SquareCompactFredholm (F := Y →ᵇ ℂ))
    (hcompact : IsCompactOperator
      (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) ^ 2 :
        (Y →ᵇ ℂ) →L[ℂ] (Y →ᵇ ℂ)))
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
  have hspec := RestrictedSpectralComparison.complementary_radius_lt
    ((scale : ℂ) • P ε) Q a b (scale * q) r
    (mul_lt_mul_of_pos_left (o.eigenvalue_re_gt hδlead ε hε) hscale) hr
    hcompare hsep hFredholm hcompact (o.vector ε)
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
