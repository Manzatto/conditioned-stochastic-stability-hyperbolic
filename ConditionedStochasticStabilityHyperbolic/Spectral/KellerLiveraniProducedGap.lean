module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniDensityApplication
public import ConditionedStochasticStabilityHyperbolic.Spectral.CompactRealLeadingPair

/-! # Actual raw spectral gap produced from KL and generalized lifting

Physical spectral pairs are constructed by the precise ordinary compact Riesz
source after algebraic simplicity is transferred. The noisy left law, pair
normalization, complementary radius and positivity orientation are outputs.
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

theorem ProjectorOutputs.exists_canonicalRawGap_of_density_and_generalized_lifting
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
    (hRiesz : CompactRealLeadingPair.ClassicalContract (X := Y))
    (hgeneral : GeneralizedSpectralComparison.Comparison ((scale : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) a b
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ))
    (hsep : GeneralizedSpectralComparison.Separates
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) b
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ))
    (f₀ : Y →ᵇ ℂ) (hf₀ : f₀ ≠ 0)
    (hident : b f₀ = a (o.vector ε))
    (hright : ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) f₀ =
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ) • f₀) :
    ∃ dc : RankOneSpectralData
      (R • strongFellerTransferOperator C hSF) (1 : Y →ᵇ ℝ),
      dc.rate = scale * (o.eigenvalue ε).re ∧ dc.mean 1 = 1 := by
  let Q := (R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF
  let rawP := R • strongFellerTransferOperator C hSF
  let r := scale * (o.eigenvalue ε).re
  have hr : 0 < r := mul_pos hscale (hq.trans (o.eigenvalue_re_gt hδlead ε hε))
  have hp := DensityStrongFeller.compact_complex_transfer_of_density
    C hSF σ k hk hk0 hkernel M hM hkM hcontinuous
  have hcompact : IsCompactOperator Q := hp.smul (R : ℂ)
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
  have hsr : (scale : ℂ) * o.eigenvalue ε = (r : ℂ) := by
    rw [o.eigenvalue_eq_real hδsub hδlead ε hε c]
    exact (Complex.ofReal_mul _ _).symm
  have hsimple := GeneralizedSpectralComparison.generalized_simple_smul (P ε)
    (o.eigenvalue ε) (scale : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt hscale))
    (o.vector ε) (o.generalized_leading_simple ε hε)
  rw [hsr] at hsimple
  exact CompactRealLeadingPair.exists_canonicalGap_of_compact_comparison hRiesz
    ((scale : ℂ) • P ε) rawP Q hcompact hcomm hpositive a b (scale * q) r
    (mul_lt_mul_of_pos_left (o.eigenvalue_re_gt hδlead ε hε) hscale) hr hcompare
    hgeneral hsep (o.vector ε) f₀ hf₀ hright hident hsimple
    (o.raw_eigenvalue_bound hδsub hδlead hq ε hε c scale hscale)
    (o.raw_peripheral_exclusion hδsub hδlead hq ε hε c scale hscale)

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
