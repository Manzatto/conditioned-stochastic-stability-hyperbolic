module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniApplication
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProjectorOrientation

/-! # Canonically oriented KL-to-local spectral application

The analytic noisy separation is derived from the primary KL outputs. The
actual continuous operator's positivity determines orientation of its leading
projector: its projection of one is nonzero and gives a nonnegative right
vector with left mass one. Thus no independently supplied `mean_one_pos`
is required by this producer of the checked local process interface.
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

/-- The complete spectral producer derives noisy analytic dominance and
canonical real orientation before constructing the local input structure.
The continuous leading pair comes from the exact common-space comparison;
no sign of its left functional is assumed. -/
theorem ProjectorOutputs.exists_canonicalComparedRawInputs
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (c : RealOperatorConjugation (P ε)) (scale : ℝ) (hscale : 0 < scale)
    (C : AbsorbingMarkovChains.CanonicalChain Y) (hSF : HasStrongFellerKernel C)
    (R : ℝ) (hR : 0 < R)
    (a : E →L[ℂ] Z) (b : (Y →ᵇ ℂ) →L[ℂ] Z) (hb : Function.Injective b)
    (hFredholm : PowerCompactGap.SquareCompactFredholm (F := Y →ᵇ ℂ))
    (hcompact : IsCompactOperator
      (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) ^ 2 :
        (Y →ᵇ ℂ) →L[ℂ] (Y →ᵇ ℂ)))
    (hcompare : ComparedSpectralGap.EigenvectorComparison ((scale : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) a b (scale * q))
    (g : Y →ᵇ ℝ) (μ : (Y →ᵇ ℝ) →L[ℝ] ℝ) (ℓ : (Y →ᵇ ℂ) →L[ℂ] ℂ)
    (hident : b (AbsorbingMarkovChains.ComplexKernel.ofReal g) = a (o.vector ε))
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ))
    (hpair : μ g = 1)
    (hright : ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hleft : ∀ f, ℓ (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) f) =
      ((scale * (o.eigenvalue ε).re : ℝ) : ℂ) * ℓ f) :
    μ 1 ≠ 0 ∧ ∃ s : ComparedLocalQuasiErgodic.ComparedRawSpectralInputs
      (A := E) (W := Z) C hSF R,
      s.rate = scale * (o.eigenvalue ε).re ∧ s.mean 1 = 1 ∧
      s.mean = (μ 1)⁻¹ • μ ∧ s.eigenvector = μ 1 • g := by
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
  have hspec := ComparedSpectralGap.complementary_radius_lt ((scale : ℂ) • P ε) Q a b
    (scale * q) r (mul_lt_mul_of_pos_left (o.eigenvalue_re_gt hδlead ε hε) hscale)
    hcompare hFredholm hcompact hb hr (o.vector ε)
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
  let α := μ 1
  have hαC : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  let γ := (α : ℂ) • o.vector ε
  let ℓc := (α⁻¹ : ℂ) • ℓ
  have hj (f : Y →ᵇ ℝ) : AbsorbingMarkovChains.ComplexKernel.ofReal (α • f) =
      (α : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal f := by
    ext x
    simp [AbsorbingMarkovChains.ComplexKernel.ofReal_apply]
  have hidentc : b (AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector) = a γ := by
    rw [hdcVector, hj, map_smul, hident, map_smul]
  have hrealc (f : Y →ᵇ ℝ) : ℓc (AbsorbingMarkovChains.ComplexKernel.ofReal f) =
      (dc.mean f : ℂ) := by
    rw [hdcMean]
    simp only [ℓc, smul_apply, smul_eq_mul, hreal, Complex.ofReal_mul, Complex.ofReal_inv]
    rfl
  have hrightc : Q (AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector) =
      (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector := by
    rw [hdcVector, hj, map_smul, hright, smul_comm]
  have hleftc (f : Y →ᵇ ℂ) : ℓc (Q f) = (r : ℂ) * ℓc f := by
    change (α⁻¹ : ℂ) * ℓ (Q f) = (r : ℂ) * ((α⁻¹ : ℂ) * ℓ f)
    rw [show ℓ (Q f) = (r : ℂ) * ℓ f from hleft f]
    ring
  have hsimplec (v : E) (hv : ((scale : ℂ) • P ε) v = (r : ℂ) • v) :
      ∃ z : ℂ, v = z • γ := by
    obtain ⟨z, hz⟩ := o.raw_leading_simple hδsub hδlead ε hε c scale hscale v hv
    refine ⟨z / (α : ℂ), ?_⟩
    change v = (z / (α : ℂ)) • ((α : ℂ) • o.vector ε)
    rw [smul_smul, div_mul_cancel₀ _ hαC]
    exact hz
  let s : ComparedLocalQuasiErgodic.ComparedRawSpectralInputs (A := E) (W := Z) C hSF R :=
    { analyticOperator := (scale : ℂ) • P ε
      analyticEmbedding := a
      continuousEmbedding := b
      embedding_injective := hb
      cutoff := scale * q
      rate := r
      cutoff_lt_rate := mul_lt_mul_of_pos_left (o.eigenvalue_re_gt hδlead ε hε) hscale
      rate_pos := hr
      fredholm := hFredholm
      square_compact := hcompact
      comparison := hcompare
      analyticVector := γ
      eigenvector := dc.eigenvector
      mean := dc.mean
      complexMean := ℓc
      vector_identification := hidentc
      real_compatibility := hrealc
      normalization := dc.mean_eigenvector
      mean_one_pos := by rw [hdcOne]; exact zero_lt_one
      right_equation := hrightc
      left_equation := hleftc
      eigenvalue_bound := o.raw_eigenvalue_bound hδsub hδlead hq ε hε c scale hscale
      peripheral_exclusion := o.raw_peripheral_exclusion hδsub hδlead hq ε hε c scale hscale
      leading_simple := hsimplec }
  exact ⟨hα, s, rfl, hdcOne, hdcMean, hdcVector⟩

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
