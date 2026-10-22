module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveEigenfunction
public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingSimplicity

/-!
# Local quasi-ergodic package for the literal noisy process

The raw continuous transfer gap and the classical plaque contracts produce
the actual QEM, its core-positive eigenfunction, geometric localization and
support-qualified uniqueness together. Normalization, the leading measure,
nonnegativity and simplicity are derived. The spectral gap and classical
geometry still need instantiation from HL; inverse-density positivity is
needed separately to show that this QEM itself supports the whole core.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.LocalQuasiErgodic

open LeanShared LocalPositiveEigenfunction Restriction
open LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]

/-- All process-level conclusions needed before the inverse support step.
Only a raw gap is supplied: its normalized counterpart is constructed. -/
theorem exists_noise_tolerance_for_local_package
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
    (w : K → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ForwardPlaqueInputs T F V K G →
      ∀ (hSF : RestrictedStrongFeller.HasStrongFellerNoise ρ F hF),
      let P := RestrictedStrongFeller.rawTransferOperator ρ F hF K hK.measurableSet
        w hw (fun x => (hwpos x).le) R hR hwR hSF
      let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw.measurable R hR hwR
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
  obtain ⟨δ, hδ, hpos⟩ := exists_noise_tolerance_for_rankOne_core_positivity
    T V K G U hV hVK hK hG hU hcoreU hUV hsep hcoreG htrans
    ρ w hw.measurable hwpos R hR hwR
  refine ⟨δ, hδ, ?_⟩
  intro F hF hclose hp hSF
  dsimp only
  intro d
  let P := RestrictedStrongFeller.transferOperator ρ F hF K hK.measurableSet
    w hw (fun x => (hwpos x).le) R hR hwR hSF
  let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw.measurable R hR hwR
  let dn := d.ofRawNormalization R hR
    (RestrictedStrongFeller.inv_smul_rawTransferOperator ρ F hF K hK.measurableSet
      w hw (fun x => (hwpos x).le) R hR hwR hSF)
  have hP (f : K →ᵇ ℝ) (x : K) : P f x = ∫ y, f y ∂C.killedTransition x :=
    RestrictedStrongFeller.transferOperator_represents ρ F hF K hK.measurableSet
      w hw (fun x => (hwpos x).le) R hR hwR hSF f x
  obtain ⟨μ, hμ, hm, hprob, hloc, hgpos⟩ := hpos F hF hclose hp P hP dn
  let _ := hμ
  have hdm : dn.mean = d.mean := by
    simp only [dn, RankOneSpectralData.ofRawNormalization_mean]
  have hdg : dn.eigenvector = d.eigenvector := by
    simp only [dn, RankOneSpectralData.ofRawNormalization_eigenvector]
  have hmraw (f : K →ᵇ ℝ) : d.mean f = ∫ y, f y ∂μ := by simpa only [hdm] using hm f
  have hg0 : ∀ x : K, 0 ≤ dn.eigenvector x :=
    dn.eigenvector_nonneg_of_positive (representedTransfer_positive C.killedTransition P hP)
  have hq : C.IsQuasiErgodic (eigenvectorMeasure μ d.eigenvector) :=
    RestrictedQuasiErgodic.raw_eigenvectorMeasure_isQuasiErgodic ρ F hF K hK.measurableSet
      w hw (fun x => (hwpos x).le) R hR hwR hSF d μ hmraw
  refine ⟨μ, hμ, hmraw, hq, hdg ▸ hloc, hdg ▸ hgpos, ?_, ?_⟩
  · intro ν hν hsupp
    have hΛ : ({x : K | x.val ∈ isolatedCore T K} : Set K).Nonempty := by
      obtain ⟨x, hx⟩ := hcore
      exact ⟨⟨x, forwardTrapped_subset T K hx.1⟩, hx⟩
    simpa only [hdg] using QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support C P hP dn μ hm hg0
      {x : K | x.val ∈ isolatedCore T K} hΛ (fun x hx => hgpos x hx) ν hν hsupp
  · exact d.leading_eigenvector_eq

end ConditionedStochasticStabilityHyperbolic.LocalQuasiErgodic
