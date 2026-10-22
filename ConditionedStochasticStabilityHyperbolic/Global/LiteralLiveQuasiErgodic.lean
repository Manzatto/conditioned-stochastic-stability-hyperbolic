module

public import ConditionedStochasticStabilityHyperbolic.Global.ConullStratumSupport
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
namespace ConditionedStochasticStabilityHyperbolic.Global.LiteralLiveQuasiErgodic
open LeanShared ComplexStrongFeller RestrictedLayerChain ConullStratumLeadingData
open ConullStratumProduct ConullStratumSupport LayerQuasiErgodic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

 theorem exists_literal_live_package
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
        (strongFeller C hSF Aᶜ hA.measurableSet.compl)) = ENNReal.ofReal dl.rate := by
  let U := Aᶜ
  have hU : MeasurableSet U := hA.measurableSet.compl
  have hz : ∀ x, C.killedTransition x Uᶜ = 0 := by simpa only [U, compl_compl] using hzeroA
  let dl := stratumData C hSF U hU hz d
  let μ := leadingMeasure C hSF d
  have hm : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ :=
    d.eigenmeasure_represents (LayerRankOne.actual_transfer_positive C hSF)
  let μl := stratumMeasure C hSF U d μ
  have hfinite : IsFiniteMeasure μl := stratumMeasure_finite C hSF U hU d μ
  let : IsFiniteMeasure μl := hfinite
  have hml : ∀ f : U →ᵇ ℝ, dl.mean f = ∫ y, f y ∂μl :=
    stratumMeasure_represents C hSF U hU hz d μ hm
  let CL := chain C U hU
  let sfL := strongFeller C hSF U hU
  have hg : ∀ x : U, 0 ≤ dl.eigenvector x :=
    dl.eigenvector_nonneg_of_positive (LayerRankOne.actual_transfer_positive CL sfL)
  let : IsFiniteKernel CL.killedTransition := ⟨⟨1, by simp, CL.killedTransition_mass_le_one⟩⟩
  have hleft := rankOne_left_eigenmeasure dl CL.killedTransition (transferOperator_apply CL sfL) μl hml
  have hq := QuasiErgodic.eigenvectorMeasure_isQuasiErgodic_of_strongFeller CL
    (transferOperator CL sfL) (transferOperator_apply CL sfL) dl μl hml hg sfL
  have hmap := map_stratum_product_eq_closed_product C hSF U hU hz d μ hm
  have hs : {x : U | x.val ∈ Λ} ⊆ (eigenvectorMeasure μl dl.eigenvector).support := by
    intro x hx
    exact core_point_mem_stratum_product_support C hSF U hU hz d μ hm x (hsupport hx)
  have hΛu : ({x : U | x.val ∈ Λ} : Set U).Nonempty := by
    obtain ⟨x, hx⟩ := hΛ
    exact ⟨⟨x, hΛlive hx⟩, hx⟩
  have hp : ∀ x ∈ ({x : U | x.val ∈ Λ} : Set U), 0 < dl.eigenvector x := by
    intro x hx
    exact stratumData_vector_pos C hSF U hU hz d x (hpositive x.val hx)
  refine ⟨dl, rfl, μl, hfinite, hml, hleft, hq, hmap, hs, ?_, ?_, dl.spectralRadius_eq_rate⟩
  · intro η hη hηsupp
    exact QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support CL
      (transferOperator CL sfL) (transferOperator_apply CL sfL) dl μl hml hg
      {x : U | x.val ∈ Λ} hΛu hp η hη hηsupp
  · exact dl.leading_eigenvector_eq

end ConditionedStochasticStabilityHyperbolic.Global.LiteralLiveQuasiErgodic
