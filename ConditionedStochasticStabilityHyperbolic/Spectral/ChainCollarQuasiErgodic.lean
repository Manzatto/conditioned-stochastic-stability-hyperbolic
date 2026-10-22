module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveCollar

/-! # Local QEM conclusions from the actual live-chain raw gap

The density-produced KL gap enters the literal chain directly. No stronger
ambient unweighted strong-Feller hypothesis is added.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.LocalCollarQuasiErgodic
open LeanShared LocalPositiveCollar Restriction
open LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]

theorem exists_noise_tolerance_for_collar_chain_package
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
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
  obtain ⟨δ, hδ, hpos⟩ := exists_noise_tolerance_for_rankOne_collar_core_positivity
    T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans
    ρ w hw.measurable hwG R hR hwR
  refine ⟨δ, hδ, ?_⟩
  intro F hF hclose hp
  dsimp only
  intro hSF d
  let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw.measurable R hR hwR
  let P := strongFellerTransferOperator C hSF
  let dn : RankOneSpectralData P (1 : K →ᵇ ℝ) := d.ofRawNormalization R hR (by
    simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hR), one_smul]
    rfl)
  have hP (f : K →ᵇ ℝ) (x : K) : P f x = ∫ y, f y ∂C.killedTransition x :=
    strongFellerTransferOperator_represents C hSF f x
  obtain ⟨μ, hμ, hm, hprob, hloc, hgpos⟩ := hpos F hF hclose hp P hP dn
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


end ConditionedStochasticStabilityHyperbolic.LocalCollarQuasiErgodic
