module

public import ConditionedStochasticStabilityHyperbolic.Global.TwoSidedSelectedGap

/-!
# Full actual selected QEM package from dominant local data and two aggregates

All global spectral/probability conclusions are constructed. The actual local
product is preserved exactly, so the produced local physical weak limit also
governs this selected measure. The two subordinate growth inputs are outputs
of the actual shifted-filtration pressure/KL producers.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.TwoSidedSelectedQuasiErgodic
open ComplexStrongFeller LayerOperators RestrictedLayerChain NestedLayerKernel
open LayerRankOne LayerQuasiErgodic LayerProductCorrespondence TwoSidedSelectedGap
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L0 L1 : Set X) (hL0 : MeasurableSet L0) (hL1 : MeasurableSet L1) (h01 : L0 ⊆ L1)
local notation "C1" => chain C L1 hL1
local notation "sf1" => strongFeller C hSF L1 hL1
local notation "A0" => innerLevel L0 L1
local notation "ha0" => hL0.preimage measurable_subtype_coe

include h01 in
/-- A genuine dominant local producer and two actual subordinate aggregates
give the selected global probability, support, uniqueness and measurable
conditioned statistics, with the original local physical product unchanged. -/
theorem exists_actual_selected_QEM_from_two_aggregates
    (hs0 : ∀ x ∈ L0, C.killedTransition x L0ᶜ = 0)
    (hs1 : ∀ x ∈ L1, ∀ᵐ y ∂C.killedTransition x, y ∈ L1)
    (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) C1 sf1 A0 ha0)
      (1 : (A0ᶜ : Set L1) →ᵇ ℝ))
    {CA CD βA βD : ℝ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD)
    (hβA : 0 ≤ βA) (hβD : 0 ≤ βD) (hArate : βA < d.rate) (hDrate : βD < d.rate)
    (hA : ∀ n : ℕ, ‖transferOperator (𝕜 := ℝ) (chain C L0 hL0)
      (strongFeller C hSF L0 hL0) ^ n‖ ≤ CA * βA ^ n)
    (hD : ∀ n : ℕ, ‖transferOperator (𝕜 := ℝ) (chain C L1ᶜ hL1.compl)
      (strongFeller C hSF L1ᶜ hL1.compl) ^ n‖ ≤ CD * βD ^ n)
    (μ : Measure (A0ᶜ : Set L1)) [IsFiniteMeasure μ]
    (hmean : ∀ f : (A0ᶜ : Set L1) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y)
    (Λ : Set (A0ᶜ : Set L1)) (hΛ : Λ.Nonempty)
    (hΛpos : ∀ y ∈ Λ, 0 < d.eigenvector y)
    (hΛsupport : Λ ⊆ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ),
      dg.rate = d.rate ∧ C.IsQuasiErgodic (productMeasure C hSF dg) ∧
      productMeasure C hSF dg = (LeanShared.eigenvectorMeasure μ d.eigenvector).map
        (fun y : (A0ᶜ : Set L1) => y.val.val) ∧
      (fun y : (A0ᶜ : Set L1) => y.val.val) '' Λ ⊆ (productMeasure C hSF dg).support ∧
      (∀ ν : Measure X, C.IsQuasiErgodic ν →
        (fun y : (A0ᶜ : Set L1) => y.val.val) '' Λ ⊆ ν.support → ν = productMeasure C hSF dg) ∧
      (∀ y : (A0ᶜ : Set L1), dg.eigenvector y.val.val = d.eigenvector y) ∧
      ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) → ∀ x,
        0 < dg.eigenvector x → Tendsto (MeasurableCanonical.pathAverage C f x) atTop
          (𝓝 (∫ y, f y ∂productMeasure C hSF dg)) := by
  obtain ⟨dg, hrate, hvector, hpair⟩ := exists_selected_data_from_two_actual_aggregates
    C hSF L0 L1 hL0 hL1 h01 hs0 hs1 d hCA hCD hβA hβD hArate hDrate hA hD
  have hq := productMeasure_isQuasiErgodic C hSF dg
  let : IsProbabilityMeasure (productMeasure C hSF dg) := hq.1
  let : IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ d.eigenvector) :=
    eigenvector_product_isProbability d μ hmean hg0
  have hmap : productMeasure C hSF dg = (LeanShared.eigenvectorMeasure μ d.eigenvector).map
      (fun y : (A0ᶜ : Set L1) => y.val.val) := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have hIntMap : (∫ x, f x ∂(LeanShared.eigenvectorMeasure μ d.eigenvector).map
        (fun y : (A0ᶜ : Set L1) => y.val.val)) =
        ∫ y, f y.val.val ∂LeanShared.eigenvectorMeasure μ d.eigenvector :=
      ((MeasurableEmbedding.subtype_coe hL1).comp
        (MeasurableEmbedding.subtype_coe (ha0).compl)).integral_map f
    calc
      _ = dg.mean (f * dg.eigenvector) := global_product_integral C hSF dg f
      _ = d.mean ((restrictOperator A0ᶜ (restrictOperator L1 f)) * d.eigenvector) := hpair f
      _ = ∫ y, f y.val.val * d.eigenvector y ∂μ :=
        hmean ((restrictOperator A0ᶜ (restrictOperator L1 f)) * d.eigenvector)
      _ = ∫ y, f y.val.val ∂LeanShared.eigenvectorMeasure μ d.eigenvector :=
        (LeanShared.integral_eigenvectorMeasure μ d.eigenvector
          d.eigenvector.continuous.measurable hg0 (fun y => f y.val.val)).symm
      _ = _ := hIntMap.symm
  have hsupport : (fun y : (A0ᶜ : Set L1) => y.val.val) '' Λ ⊆ (productMeasure C hSF dg).support := by
    rw [hmap]
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hx
    have hm : ((LeanShared.eigenvectorMeasure μ d.eigenvector).map
        (Subtype.val : (A0ᶜ : Set L1) → L1)).map (Subtype.val : L1 → X) =
        (LeanShared.eigenvectorMeasure μ d.eigenvector).map (fun y => y.val.val) :=
      Measure.map_map measurable_subtype_coe measurable_subtype_coe
    rw [← hm]
    exact subtype_support_maps_into _ (subtype_support_maps_into _ (hΛsupport hp))
  refine ⟨dg, hrate, hq, hmap, hsupport, ?_, hvector, ?_⟩
  · intro ν hν hsupp
    obtain ⟨p, hp⟩ := hΛ
    apply QuasiErgodic.eq_eigenvectorMeasure_of_support C
      (transferOperator C hSF) (transferOperator_apply C hSF) dg
      (leadingMeasure C hSF dg) (dg.eigenmeasure_represents (actual_transfer_positive C hSF))
      (dg.eigenvector_nonneg_of_positive (actual_transfer_positive C hSF)) ν hν
      p.val.val (hsupp ⟨p, hp, rfl⟩)
    rw [hvector p]
    exact hΛpos p hp
  · intro f hf hb x hx
    exact conditioned_average_limit C hSF dg f hf hb x hx

end ConditionedStochasticStabilityHyperbolic.Global.TwoSidedSelectedQuasiErgodic
