module

public import ConditionedStochasticStabilityHyperbolic.Global.LiteralLiveQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.LayerQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingEigenmeasure
public import ConditionedStochasticStabilityHyperbolic.Spectral.Normalization

/-! # The ambient selected process gives the literal closed live-state result

The global process is killed on entering A. Its structural zero target mass
on A transfers the produced ambient gap and leading measure to Aᶜ, constructs
the literal live QEM, and preserves the physical probability under inclusion.
No reference-nullness of A and no new live spectral gap are assumed.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Global.LiteralLiveCompleteSpectral
open LeanShared ComplexStrongFeller RestrictedLayerChain ConullStratumLeadingData
open ConullStratumProduct ConullStratumSupport LayerQuasiErgodic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_literal_live_package_with_left_uniqueness
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (A : Set X) (hA : IsOpen A) (hzeroA : ∀ x, C.killedTransition x A = 0)
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ))
    (Λ : Set X) (hΛ : Λ.Nonempty) (hΛlive : Λ ⊆ Aᶜ)
    (hpositive : ∀ x ∈ Λ, 0 < d.eigenvector x)
    (hsupport : Λ ⊆ (productMeasure C hSF d).support) :
    ∃ dl : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (chain C Aᶜ hA.measurableSet.compl)
      (strongFeller C hSF Aᶜ hA.measurableSet.compl)) (1 : ↥(Aᶜ) →ᵇ ℝ),
      dl.rate = d.rate ∧
    ∃ μ : Measure ↥(Aᶜ), IsFiniteMeasure μ ∧
      (∀ f : ↥(Aᶜ) →ᵇ ℝ, dl.mean f = ∫ y, f y ∂μ) ∧
      (chain C Aᶜ hA.measurableSet.compl).killedTransition ∘ₘ μ = ENNReal.ofReal dl.rate • μ ∧
      (chain C Aᶜ hA.measurableSet.compl).IsQuasiErgodic (eigenvectorMeasure μ dl.eigenvector) ∧
      (eigenvectorMeasure μ dl.eigenvector).map Subtype.val = productMeasure C hSF d ∧
      {x : ↥(Aᶜ) | x.val ∈ Λ} ⊆ (eigenvectorMeasure μ dl.eigenvector).support ∧
      (∀ η : Measure ↥(Aᶜ), (chain C Aᶜ hA.measurableSet.compl).IsQuasiErgodic η →
        {x : ↥(Aᶜ) | x.val ∈ Λ} ⊆ η.support → η = eigenvectorMeasure μ dl.eigenvector) ∧
      (∀ f : ↥(Aᶜ) →ᵇ ℝ,
        transferOperator (𝕜 := ℝ) (chain C Aᶜ hA.measurableSet.compl)
          (strongFeller C hSF Aᶜ hA.measurableSet.compl) f = dl.rate • f →
        f = dl.mean f • dl.eigenvector) ∧
      spectralRadius ℝ (transferOperator (𝕜 := ℝ) (chain C Aᶜ hA.measurableSet.compl)
        (strongFeller C hSF Aᶜ hA.measurableSet.compl)) = ENNReal.ofReal dl.rate ∧
      (∀ (ν : Measure ↥(Aᶜ)) [IsFiniteMeasure ν],
        (chain C Aᶜ hA.measurableSet.compl).killedTransition ∘ₘ ν = ENNReal.ofReal dl.rate • ν →
        ν = ENNReal.ofReal (∫ x, dl.eigenvector x ∂ν) • μ) ∧
      (∀ (ν : Measure ↥(Aᶜ)) [IsFiniteMeasure ν],
        (chain C Aᶜ hA.measurableSet.compl).killedTransition ∘ₘ ν = ENNReal.ofReal dl.rate • ν →
        (∫ x, dl.eigenvector x ∂ν) = 1 → ν = μ) := by
  obtain ⟨dl, hrate, μ, hμ, hm, hleft, hqem, hmap, hs, huniq, hright, hradius⟩ :=
    LiteralLiveQuasiErgodic.exists_literal_live_package C hSF A hA hzeroA d Λ hΛ hΛlive hpositive hsupport
  let : IsFiniteMeasure μ := hμ
  let CL := chain C Aᶜ hA.measurableSet.compl
  let sfL := strongFeller C hSF Aᶜ hA.measurableSet.compl
  let : IsFiniteKernel CL.killedTransition := ⟨⟨1, by simp, CL.killedTransition_mass_le_one⟩⟩
  have hg : ∀ x : ↥(Aᶜ), 0 ≤ dl.eigenvector x :=
    dl.eigenvector_nonneg_of_positive (LayerRankOne.actual_transfer_positive CL sfL)
  refine ⟨dl, hrate, μ, hμ, hm, hleft, hqem, hmap, hs, huniq, hright, hradius, ?_, ?_⟩
  · intro ν _ hν
    exact leading_eigenmeasure_eq_smul dl CL.killedTransition (transferOperator_apply CL sfL) μ hm hg ν hν
  · intro ν _ hν hn
    exact leading_eigenmeasure_eq_of_normalization dl CL.killedTransition
      (transferOperator_apply CL sfL) μ hm hg ν hν hn

end ConditionedStochasticStabilityHyperbolic.Global.LiteralLiveCompleteSpectral
