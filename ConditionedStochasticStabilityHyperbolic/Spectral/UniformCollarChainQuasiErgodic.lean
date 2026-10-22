module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ChainCollarQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.UniformLocalPositiveCollar
public import ConditionedStochasticStabilityHyperbolic.Spectral.FullCollarChainQuasiErgodic

/-! One geometric tolerance for every probability noise law. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.UniformLocalCollarQuasiErgodic
open LeanShared LocalPositiveCollar Restriction
open LeanShared.ControlledPlaqueClosure
variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]

theorem exists_uniform_noise_tolerance_for_collar_chain_package
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure],
      ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ForwardCollarPlaqueInputs T F V K G →
      let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw.measurable R hR hwR
      ∀ (hSF : HasStrongFellerKernel C),
      let P := R • strongFellerTransferOperator C hSF
      ∀ d : RankOneSpectralData P (1 : K →ᵇ ℝ),
      ∃ μ : Measure K, IsFiniteMeasure μ ∧
        (∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) ∧
        C.IsQuasiErgodic (eigenvectorMeasure μ d.eigenvector) ∧
        (eigenvectorMeasure μ d.eigenvector).support ⊆ retainedRegion K U ∧
        (∀ x : K, x.val ∈ isolatedCore T K → 0 < d.eigenvector x) ∧
        (∀ ν : Measure K, C.IsQuasiErgodic ν →
          {x : K | x.val ∈ isolatedCore T K} ⊆ ν.support →
          ν = eigenvectorMeasure μ d.eigenvector) ∧
        (∀ v : K →ᵇ ℝ, P v = d.rate • v → v = d.mean v • d.eigenvector) := by
  obtain ⟨δ, hδ, hpos⟩ := UniformLocalPositiveCollar.exists_uniform_noise_tolerance_for_rankOne_collar_core_positivity
    (Ω := Ω) T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans
    w hw.measurable hwG R hR hwR
  refine ⟨δ, hδ, ?_⟩
  intro ρ _ _ F hF hclose hp
  dsimp only
  intro hSF d
  let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw.measurable R hR hwR
  let P := strongFellerTransferOperator C hSF
  let dn : RankOneSpectralData P (1 : K →ᵇ ℝ) := d.ofRawNormalization R hR (by
    simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hR), one_smul]
    rfl)
  have hP (f : K →ᵇ ℝ) (x : K) : P f x = ∫ y, f y ∂C.killedTransition x :=
    strongFellerTransferOperator_represents C hSF f x
  obtain ⟨μ, hμ, hm, hprob, hloc, hgpos⟩ := hpos ρ F hF hclose hp P hP dn
  let _ := hμ
  have hdm : dn.mean = d.mean := by
    simp only [dn, RankOneSpectralData.ofRawNormalization_mean]
  have hdg : dn.eigenvector = d.eigenvector := by
    simp only [dn, RankOneSpectralData.ofRawNormalization_eigenvector]
  have hmraw (f : K →ᵇ ℝ) : d.mean f = ∫ y, f y ∂μ := by simpa only [hdm] using hm f
  have hg0 : ∀ x : K, 0 ≤ dn.eigenvector x :=
    dn.eigenvector_nonneg_of_positive (representedTransfer_positive C.killedTransition P hP)
  have hq : C.IsQuasiErgodic (eigenvectorMeasure μ d.eigenvector) := by
    rw [← hdg]
    exact QuasiErgodic.strongFeller_rankOne_isQuasiErgodic C hSF dn μ hm hg0
  refine ⟨μ, hμ, hmraw, hq, hdg ▸ hloc, hdg ▸ hgpos, ?_, ?_⟩
  · intro ν hν hsupp
    have hΛ : ({x : K | x.val ∈ isolatedCore T K} : Set K).Nonempty := by
      obtain ⟨x, hx⟩ := hcore
      exact ⟨⟨x, forwardTrapped_subset T K hx.1⟩, hx⟩
    simpa only [hdg] using QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support C P hP dn μ hm hg0
      {x : K | x.val ∈ isolatedCore T K} hΛ (fun x hx => hgpos x hx) ν hν hsupp
  · exact d.leading_eigenvector_eq


theorem exists_uniform_noise_tolerance_for_full_collar_chain_package
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (noise : Measure Ω) [IsProbabilityMeasure noise] [noise.IsOpenPosMeasure],
      ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ForwardCollarPlaqueInputs T F V K G →
      let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
      ∀ (hSF : HasStrongFellerKernel C),
      let P := R • strongFellerTransferOperator C hSF
      ∀ d : RankOneSpectralData P (1 : K →ᵇ ℝ),
      CollarDensityCertificate.Inputs T V K G hK noise F hF w hw.measurable R δ →
      ∃ ν : Measure K, IsFiniteMeasure ν ∧
        (∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂ν) ∧
        C.IsQuasiErgodic (eigenvectorMeasure ν d.eigenvector) ∧
        (eigenvectorMeasure ν d.eigenvector).support ⊆ retainedRegion K U ∧
        (∀ x : K, x.val ∈ isolatedCore T K → 0 < d.eigenvector x) ∧
        ({x : K | x.val ∈ isolatedCore T K} ⊆ (eigenvectorMeasure ν d.eigenvector).support) ∧
        (∀ η : Measure K, C.IsQuasiErgodic η →
          {x : K | x.val ∈ isolatedCore T K} ⊆ η.support → η = eigenvectorMeasure ν d.eigenvector) ∧
        (∀ v : K →ᵇ ℝ, P v = d.rate • v → v = d.mean v • d.eigenvector) ∧
        spectralRadius ℝ P = ENNReal.ofReal d.rate := by
  obtain ⟨δf, hδf, hlocal⟩ := exists_uniform_noise_tolerance_for_collar_chain_package
    (Ω := Ω) T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore w hw hwG R hR hwR
  have hcoreV : isolatedCore T K ⊆ V := hcoreU.trans (subset_closure.trans hUV)
  obtain ⟨δi, hδi, hinverse⟩ :=
    ComparedCollarSupport.exists_noise_tolerance_for_inverse_collar_support_from_actual_data
      (Ω := Ω) T V K G U hV hVK hK hcoreV hcoreG htrans hUV hUG
  refine ⟨min δf δi, lt_min hδf hδi, ?_⟩
  intro noise _ _ F hF hclose hp
  dsimp only
  intro hSF d c
  obtain ⟨ν, hν, hm, hq, hloc, hgpos, hunique, hsimp⟩ := hlocal noise F hF
    (fun x hx ω => (hclose x hx ω).trans_le (min_le_left _ _)) hp hSF d
  let : IsFiniteMeasure ν := hν
  let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
  let P := strongFellerTransferOperator C hSF
  let dn : RankOneSpectralData P (1 : K →ᵇ ℝ) := d.ofRawNormalization R hR (by
    simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hR), one_smul]
    rfl)
  have hdnμ : dn.mean = d.mean := d.ofRawNormalization_mean _ _ _
  have hdng : dn.eigenvector = d.eigenvector := d.ofRawNormalization_eigenvector _ _ _
  obtain ⟨cert⟩ := CollarDensityCertificate.exists_certificate_of_chain_data
    T V K G hK noise F hF w hw R hR hwR hSF dn ν
    (by simpa only [hdnμ] using hm) (min δf δi) c
  let : IsFiniteMeasure cert.reference := cert.reference_finite
  have hsupport := hinverse noise F hF w hw.measurable R hR hwR hSF dn ν
    (by simpa only [hdnμ] using hm) (by simpa only [hdng] using hloc)
    (by simpa only [hdng] using hgpos) cert.inverseMap cert.inverse_measurable
    (fun x hx ω => (cert.inverse_close x hx ω).trans_le (min_le_right _ _)) cert.inverse_plaques
    cert.inverseWeight cert.weight_measurable cert.weightBound cert.weight_bounded cert.weight_positive
    cert.reference cert.density cert.reference_support cert.density_measurable
    cert.density_nonnegative cert.density_continuous cert.density_representation
    cert.duality cert.inverse_density_continuous
  exact ⟨ν, hν, hm, hq, hloc, hgpos, by simpa only [hdng] using hsupport,
    hunique, hsimp, d.spectralRadius_eq_rate⟩

end ConditionedStochasticStabilityHyperbolic.UniformLocalCollarQuasiErgodic
