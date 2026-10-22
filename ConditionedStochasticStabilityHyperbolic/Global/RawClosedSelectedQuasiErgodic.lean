module

public import ConditionedStochasticStabilityHyperbolic.Global.ClosedSelectedQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalChainGap

/-! # Raw pressure bounds and raw produced local data give the actual QEM -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.RawClosedSelectedQuasiErgodic
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel LayerQuasiErgodic ClosedDominantSource

private theorem normalized_power_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (R : ℝ) (hR : 0 < R) (B β : ℝ)
    (hpow : ∀ n : ℕ, ‖(R • P)^n‖ ≤ B * β^n) :
    ∀ n : ℕ, ‖P^n‖ ≤ B * (β / R)^n := by
  intro n
  have h := hpow n
  rw [smul_pow, norm_smul, Real.norm_of_nonneg (pow_nonneg hR.le n)] at h
  calc
    ‖P^n‖ ≤ (B * β^n) / R^n :=
      (le_div_iff₀ (pow_pos hR n)).mpr ((mul_comm _ _).trans_le h)
    _ = B * (β / R)^n := by rw [div_pow]; ring

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L0 L1 : Set X) (hL0 : MeasurableSet L0) (hL1 : MeasurableSet L1) (h01 : L0 ⊆ L1)

include h01 in
theorem exists_selected_QEM_from_raw_closed_local
    (hs0 : ∀ x ∈ L0, C.killedTransition x L0ᶜ = 0)
    (hs1 : ∀ x ∈ L1, ∀ᵐ y ∂C.killedTransition x, y ∈ L1)
    (hzero : ∀ x : (closure (L1 \ L0) : Set X),
      (chain C (closure (L1 \ L0)) (closureLayer_measurable L0 L1)).killedTransition x
        (innerLevel (L1 \ L0) (closure (L1 \ L0)))ᶜ = 0)
    (R : ℝ) (hR : 0 < R)
    (d : RankOneSpectralData
      (R • transferOperator (𝕜 := ℝ) (chain C (closure (L1 \ L0)) (closureLayer_measurable L0 L1))
        (strongFeller C hSF (closure (L1 \ L0)) (closureLayer_measurable L0 L1)))
      (1 : (closure (L1 \ L0) : Set X) →ᵇ ℝ))
    {CA CD βA βD : ℝ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD)
    (hβA : 0 ≤ βA) (hβD : 0 ≤ βD) (hArate : βA < d.rate) (hDrate : βD < d.rate)
    (hA : ∀ n : ℕ, ‖(R • transferOperator (𝕜 := ℝ) (chain C L0 hL0)
      (strongFeller C hSF L0 hL0)) ^ n‖ ≤ CA * βA ^ n)
    (hD : ∀ n : ℕ, ‖(R • transferOperator (𝕜 := ℝ) (chain C L1ᶜ hL1.compl)
      (strongFeller C hSF L1ᶜ hL1.compl)) ^ n‖ ≤ CD * βD ^ n)
    (μ : Measure (closure (L1 \ L0) : Set X)) [IsFiniteMeasure μ]
    (hmean : ∀ f : (closure (L1 \ L0) : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y)
    (Λ : Set (L1 \ L0 : Set X)) (hΛ : Λ.Nonempty)
    (hΛpos : ∀ y ∈ Λ, 0 < d.eigenvector ⟨y.val, subset_closure y.property⟩)
    (hΛsupport : ∀ y ∈ Λ, (⟨y.val, subset_closure y.property⟩ : (closure (L1 \ L0) : Set X)) ∈
      (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ),
      dg.rate = R⁻¹ * d.rate ∧ C.IsQuasiErgodic (productMeasure C hSF dg) ∧
      productMeasure C hSF dg = (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val ∧
      Subtype.val '' Λ ⊆ (productMeasure C hSF dg).support ∧
      (∀ ν : Measure X, C.IsQuasiErgodic ν → Subtype.val '' Λ ⊆ ν.support →
        ν = productMeasure C hSF dg) ∧
      (∀ y : (L1 \ L0 : Set X), dg.eigenvector y.val =
        (R⁻¹ * d.rate)⁻¹ * d.eigenvector ⟨y.val, subset_closure y.property⟩) ∧
      ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) → ∀ x,
        0 < dg.eigenvector x → Tendsto (MeasurableCanonical.pathAverage C f x) atTop
          (𝓝 (∫ y, f y ∂productMeasure C hSF dg)) := by
  let dn := d.ofRawNormalization R hR (by
    rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul])
  have hr : dn.rate = R⁻¹ * d.rate := d.ofRawNormalization_rate R hR _
  have hm : ∀ f, dn.mean f = ∫ y, f y ∂μ := by
    intro f
    simpa only [dn, RankOneSpectralData.ofRawNormalization_mean] using hmean f
  have ha : βA / R < dn.rate := by
    rw [hr, mul_comm R⁻¹ d.rate, ← div_eq_mul_inv]
    exact (div_lt_div_iff_of_pos_right hR).mpr hArate
  have hd : βD / R < dn.rate := by
    rw [hr, mul_comm R⁻¹ d.rate, ← div_eq_mul_inv]
    exact (div_lt_div_iff_of_pos_right hR).mpr hDrate
  obtain ⟨dg, hrate, hq, hproduct, hsupp, huniq, hv, hlim⟩ :=
    ClosedSelectedQuasiErgodic.exists_selected_QEM_from_closed_local
      C hSF L0 L1 hL0 hL1 h01 hs0 hs1 hzero dn hCA hCD
      (div_nonneg hβA hR.le) (div_nonneg hβD hR.le) ha hd
      (normalized_power_bound _ R hR CA βA hA)
      (normalized_power_bound _ R hR CD βD hD) μ hm
      (by simpa only [dn, RankOneSpectralData.ofRawNormalization_eigenvector] using hg0)
      Λ hΛ
      (by simpa only [dn, RankOneSpectralData.ofRawNormalization_eigenvector] using hΛpos)
      (by simpa only [dn, RankOneSpectralData.ofRawNormalization_eigenvector] using hΛsupport)
  refine ⟨dg, hrate.trans hr, hq, ?_, hsupp, huniq, ?_, hlim⟩
  · simpa only [dn, RankOneSpectralData.ofRawNormalization_eigenvector] using hproduct
  · intro y
    simpa only [hr, dn, RankOneSpectralData.ofRawNormalization_eigenvector] using hv y

end ConditionedStochasticStabilityHyperbolic.Global.RawClosedSelectedQuasiErgodic
