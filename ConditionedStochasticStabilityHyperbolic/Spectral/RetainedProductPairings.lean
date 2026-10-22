module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingSimplicity
public import ConditionedStochasticStabilityHyperbolic.Spectral.PositiveEigenmeasure
public import ConditionedStochasticStabilityHyperbolic.Restriction.HarmonicProductRestriction
public import ConditionedStochasticStabilityHyperbolic.Restriction.WeightAgreement
public import LeanShared.Probability.EigenvectorMeasure
public import Mathlib.Topology.Algebra.Module.Basic

/-! # Normalized product coefficients through retained regions

Harmonic-weighted power restriction identifies normalized product pairings
without identifying the raw left measures. Scalar differences between right
vectors cancel in the two normalized rank-one limits. A separate common-core
projector identity transfers the cutoff continuous product to the analytic
spectral pairing. These are operator identities before measure integration;
no desired probability pairing or measure limit is an input.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace ConditionedStochasticStabilityHyperbolic.RetainedProductPairings

section RealPowers

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {P : E →L[ℝ] E} {Q : H →L[ℝ] H} {one : E} {oneRet : H}

/-- Gap limits turn actual power restriction for a harmonic-weighted test
into equality of normalized product coefficients. The left measures
can differ outside and even on the retained region. -/
theorem coefficient_eq_of_weighted_power_restriction
    (d : RankOneSpectralData P one) (e : RankOneSpectralData Q oneRet)
    (hRate : d.rate = e.rate) (R : E →L[ℝ] H) (c : ℝ) (hc : c ≠ 0)
    (hg : R d.eigenvector = c • e.eigenvector)
    (f : E) (fRet : H) (hf : R f = c • fRet)
    (hpower : ∀ n : ℕ, R ((P ^ n) f) = (Q ^ n) (R f)) :
    d.mean f = e.mean fRet := by
  have hnorm (n : ℕ) : R ((d.normalizedOperator ^ n) f) =
      (e.normalizedOperator ^ n) (R f) := by
    simp only [RankOneSpectralData.normalizedOperator, smul_pow, smul_apply, map_smul,
      hpower, hRate]
  have hleft := R.continuous.continuousAt.tendsto.comp
    ((ContinuousLinearMap.apply ℝ E f).continuous.continuousAt.tendsto.comp d.tendsto_powers)
  have hright := (ContinuousLinearMap.apply ℝ H (R f)).continuous.continuousAt.tendsto.comp e.tendsto_powers
  have hright' : Tendsto (fun n => R ((d.normalizedOperator ^ n) f)) atTop
      (𝓝 (e.projection (R f))) := by
    apply hright.congr'
    exact Eventually.of_forall (fun n => (hnorm n).symm)
  have he : R (d.projection f) = e.projection (R f) := tendsto_nhds_unique hleft hright'
  simp only [RankOneSpectralData.projection, ContinuousLinearMap.smulRight_apply,
    map_smul, hg, hf, smul_smul] at he
  have hs := (smul_left_injective ℝ e.eigenvector_ne_zero) he
  apply mul_right_cancel₀ hc
  simpa only [mul_comm] using hs

end RealPowers

section ActualChain

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
open Restriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Actual no-return and finite-extinction geometry identifies the harmonic
product coefficient. Power restriction is derived from the killed kernel,
rather than supplied as an operator or desired pairing hypothesis. -/
theorem coefficient_eq_of_actual_retained_chain
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (V B : Set X) (hV : MeasurableSet V)
    (hreturn : ∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ B)
    (hext : ∀ x ∈ B, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF)
      (1 : X →ᵇ ℝ))
    (e : RankOneSpectralData (smoothedSubtypeTransfer (𝕜 := ℝ) C hSF V hV)
      (1 : V →ᵇ ℝ))
    (hRate : d.rate = e.rate) (c : ℝ) (hc : c ≠ 0)
    (hg : restrictObservable V d.eigenvector = c • e.eigenvector)
    (h : X →ᵇ ℝ) :
    d.mean (d.eigenvector * h) =
      e.mean (e.eigenvector * restrictObservable V h) := by
  have hpos : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF f x := by
    intro f hf x
    rw [ComplexStrongFeller.transferOperator_apply]
    exact integral_nonneg hf
  have hnonneg : 0 ≤ d.eigenvector := d.eigenvector_nonneg_of_positive hpos
  have hproduct : restrictObservable V (d.eigenvector * h) =
      c • (e.eigenvector * restrictObservable V h) := by
    change restrictObservable V d.eigenvector * restrictObservable V h = _
    rw [hg, smul_mul_assoc]
  apply coefficient_eq_of_weighted_power_restriction d e hRate
    (restrictObservable V) c hc hg _ _ hproduct
  intro n
  simpa only [show restrictObservable V (d.eigenvector * h) =
      restrictObservable V d.eigenvector * restrictObservable V h from rfl] using
    restrict_actual_harmonic_product_power C hSF V B hV hreturn hext
      d.eigenvector h hnonneg d.rate (ne_of_gt d.rate_pos) d.right_eigenvector n

/-- The coefficient identity yields the actual normalized product-measure
pairing. The raw left measures themselves need not coincide. -/
theorem integral_product_eq_of_actual_retained_chain
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (V B : Set X) (hV : MeasurableSet V)
    (hreturn : ∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ B)
    (hext : ∀ x ∈ B, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF)
      (1 : X →ᵇ ℝ))
    (e : RankOneSpectralData (smoothedSubtypeTransfer (𝕜 := ℝ) C hSF V hV)
      (1 : V →ᵇ ℝ))
    (hRate : d.rate = e.rate) (c : ℝ) (hc : c ≠ 0)
    (hg : restrictObservable V d.eigenvector = c • e.eigenvector)
    (μ : Measure X) (η : Measure V)
    (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)
    (hη : ∀ f : V →ᵇ ℝ, e.mean f = ∫ x, f x ∂η)
    (h : X →ᵇ ℝ) :
    (∫ x, h x ∂LeanShared.eigenvectorMeasure μ d.eigenvector) =
      ∫ x, restrictObservable V h x ∂LeanShared.eigenvectorMeasure η e.eigenvector := by
  have hpos : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF f x := by
    intro f hf x
    rw [ComplexStrongFeller.transferOperator_apply]
    exact integral_nonneg hf
  have hposRet : ∀ f : V →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ smoothedSubtypeTransfer (𝕜 := ℝ) C hSF V hV f x := by
    intro f hf x
    rw [smoothedSubtypeTransfer_represents]
    exact integral_nonneg hf
  rw [LeanShared.integral_eigenvectorMeasure μ d.eigenvector
      d.eigenvector.continuous.measurable (d.eigenvector_nonneg_of_positive hpos),
    LeanShared.integral_eigenvectorMeasure η e.eigenvector
      e.eigenvector.continuous.measurable (e.eigenvector_nonneg_of_positive hposRet)]
  have heq := coefficient_eq_of_actual_retained_chain C hSF V B hV hreturn hext
    d e hRate c hc hg h
  rw [hμ, hη] at heq
  simpa only [BoundedContinuousFunction.mul_apply, mul_comm] using heq

/-- Different departure weights with the same retained kernel yield the same
normalized harmonic-product coefficient. Only the retained right vectors
are matched; the full right functions and left measures can differ. -/
theorem coefficient_eq_of_two_actual_weights
    (C D : AbsorbingMarkovChains.CanonicalChain X)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
    (V BC BD : Set X) (hV : MeasurableSet V)
    (hreturnC : ∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ BC)
    (hextC : ∀ x ∈ BC, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (hreturnD : ∀ x : V, ∀ᵐ y ∂D.killedTransition x.val, y ∉ V → y ∈ BD)
    (hextD : ∀ x ∈ BD, ∃ n : ℕ,
      D.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (hkernel : LeanShared.SubtypeKernel.restrict C.killedTransition V hV =
      LeanShared.SubtypeKernel.restrict D.killedTransition V hV)
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hC)
      (1 : X →ᵇ ℝ))
    (e : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD)
      (1 : X →ᵇ ℝ))
    (hRate : d.rate = e.rate) (c : ℝ) (hc : c ≠ 0)
    (hg : restrictObservable V d.eigenvector = c • restrictObservable V e.eigenvector)
    (hne : restrictObservable V e.eigenvector ≠ 0) (h : X →ᵇ ℝ) :
    d.mean (d.eigenvector * h) = e.mean (e.eigenvector * h) := by
  have posC : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hC f x := by
    intro f hf x
    rw [ComplexStrongFeller.transferOperator_apply]
    exact integral_nonneg hf
  have posD : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD f x := by
    intro f hf x
    rw [ComplexStrongFeller.transferOperator_apply]
    exact integral_nonneg hf
  have hp (n : ℕ) : restrictObservable V
      ((d.normalizedOperator ^ n) (d.eigenvector * h)) =
      c • restrictObservable V ((e.normalizedOperator ^ n) (e.eigenvector * h)) := by
    simp only [RankOneSpectralData.normalizedOperator, smul_pow, smul_apply, map_smul]
    rw [restrict_actual_harmonic_product_power C hC V BC hV hreturnC hextC
      d.eigenvector h (d.eigenvector_nonneg_of_positive posC) d.rate
      (ne_of_gt d.rate_pos) d.right_eigenvector n,
      restrict_actual_harmonic_product_power D hD V BD hV hreturnD hextD
      e.eigenvector h (e.eigenvector_nonneg_of_positive posD) e.rate
      (ne_of_gt e.rate_pos) e.right_eigenvector n,
      smoothedSubtypeTransfer_eq_of_kernel_eq C D hC hD V hV hkernel,
      hg, smul_mul_assoc, map_smul, hRate]
    exact smul_comm _ _ _
  have hd := (restrictObservable V).continuous.continuousAt.tendsto.comp
    ((ContinuousLinearMap.apply ℝ (X →ᵇ ℝ) (d.eigenvector * h)).continuous.continuousAt.tendsto.comp
      d.tendsto_powers)
  have he := (restrictObservable V).continuous.continuousAt.tendsto.comp
    ((ContinuousLinearMap.apply ℝ (X →ᵇ ℝ) (e.eigenvector * h)).continuous.continuousAt.tendsto.comp
      e.tendsto_powers)
  have hes := he.const_smul c
  have hes' : Tendsto (fun n => restrictObservable V
      ((d.normalizedOperator ^ n) (d.eigenvector * h))) atTop
      (𝓝 (c • restrictObservable V (e.projection (e.eigenvector * h)))) :=
    hes.congr' (Eventually.of_forall (fun n => (hp n).symm))
  have hh := tendsto_nhds_unique hd hes'
  simp only [ContinuousLinearMap.apply_apply, RankOneSpectralData.projection,
    ContinuousLinearMap.smulRight_apply, map_smul, hg, smul_smul] at hh
  have hs := (smul_left_injective ℝ hne) hh
  apply mul_right_cancel₀ hc
  simpa only [mul_comm] using hs

end ActualChain

section CommonCore

variable {A F W Core : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Common smooth-core Riesz-projector agreement and actual multiplication
core identifications determine the normalized coefficient. Neither a left
functional agreement nor a physical product integral is assumed. -/
theorem coefficient_eq_of_common_core_projectors
    (Pa : A →L[ℂ] A) (Pp : F →L[ℂ] F)
    (μa : A →L[ℂ] ℂ) (μp : F →L[ℂ] ℂ) (ga : A) (gp : F)
    (hPa : Pa = μa.smulRight ga) (hPp : Pp = μp.smulRight gp)
    (a : A →L[ℂ] W) (b : F →L[ℂ] W)
    (Ia : Core → A) (Ip : Core → F)
    (hprojectors : ∀ u, b (Pp (Ip u)) = a (Pa (Ia u)))
    (c : ℂ) (hc : c ≠ 0) (hg : b gp = c • a ga) (hga : a ga ≠ 0)
    (fa : A) (fp : F)
    (hcore : ∃ u : Core, Ip u = fp ∧ Ia u = c • fa) :
    μp fp = μa fa := by
  obtain ⟨u, hup, hua⟩ := hcore
  have he := hprojectors u
  rw [hup, hua, hPa, hPp, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, map_smul, hg, map_smul,
    map_smul, smul_smul, smul_eq_mul] at he
  have hs := (smul_left_injective ℂ hga) he
  apply mul_right_cancel₀ hc
  simpa only [mul_comm] using hs

end CommonCore

end ConditionedStochasticStabilityHyperbolic.RetainedProductPairings
