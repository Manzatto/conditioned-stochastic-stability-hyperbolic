module
public import ConditionedStochasticStabilityHyperbolic.Global.ConullLocalQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.NestedProductCoordinates

/-! Closed-local data descend to the DIRECT ambient stratum, with its exact
physical probability. Both conull deletion and nested-subtype flattening
are constructed, and the literal stratum need not be compact. -/
public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.FlattenedConullLocalQuasiErgodic
open LeanShared ComplexStrongFeller RestrictedLayerChain NestedLayerKernel
open ConullStratumLeadingData NestedDirectLeadingData NestedProductCoordinates

theorem exists_direct_stratum_QEM
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)
    (U V : Set X) (hUV : U ⊆ V) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hzero : ∀ x, (chain C V hV).killedTransition x (innerLevel U V)ᶜ = 0)
    (d : RankOneSpectralData
      (transferOperator (𝕜 := ℝ) (chain C V hV) (strongFeller C sf V hV)) (1 : V →ᵇ ℝ))
    (μ : Measure V) [IsFiniteMeasure μ]
    (mean : ∀ f : V →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)
    (nonneg : ∀ x, 0 ≤ d.eigenvector x)
    (core : Set X) (nonempty : core.Nonempty) (coreU : core ⊆ U)
    (positive : ∀ x : V, x.val ∈ core → 0 < d.eigenvector x)
    (support : ∀ x : V, x.val ∈ core → x ∈ (eigenvectorMeasure μ d.eigenvector).support) :
    ∃ ν : ProbabilityMeasure U,
      (ν : Measure U).map Subtype.val = (eigenvectorMeasure μ d.eigenvector).map Subtype.val ∧
      (chain C U hU).IsQuasiErgodic (ν : Measure U) ∧
      {x : U | x.val ∈ core} ⊆ (ν : Measure U).support ∧
      ∀ ζ : Measure U, (chain C U hU).IsQuasiErgodic ζ →
        {x : U | x.val ∈ core} ⊆ ζ.support → ζ = (ν : Measure U) := by
  let CV := chain C V hV
  let sfV := strongFeller C sf V hV
  let hmU := hU.preimage (measurable_subtype_coe : Measurable (Subtype.val : V → X))
  let dm := stratumData CV sfV (innerLevel U V) hmU hzero d
  let μm := stratumMeasure CV sfV (innerLevel U V) d μ
  let : IsFiniteMeasure μm := stratumMeasure_finite CV sfV (innerLevel U V) hmU d μ
  have hm : ∀ f, dm.mean f = ∫ x, f x ∂μm :=
    stratumMeasure_represents CV sfV (innerLevel U V) hmU hzero d μ mean
  let dd := directData U V hUV C sf hU hV dm
  let μd := μm.map (flatten U V hUV)
  let : IsFiniteMeasure μd := Measure.isFiniteMeasure_map _ _
  have hd : ∀ f, dd.mean f = ∫ x, f x ∂μd :=
    directData_represents U V hUV C sf hU hV dm μm hm
  have hn : ∀ x, 0 ≤ dd.eigenvector x := by
    intro x
    exact mul_nonneg (inv_nonneg.mpr d.rate_pos.le) (nonneg _)
  have : IsProbabilityMeasure (eigenvectorMeasure μd dd.eigenvector) :=
    eigenvector_product_isProbability dd μd hd hn
  let ν : ProbabilityMeasure U := ⟨eigenvectorMeasure μd dd.eigenvector, inferInstance⟩
  have hproduct : eigenvectorMeasure μd dd.eigenvector =
      (eigenvectorMeasure μm dm.eigenvector).map (flatten U V hUV) :=
    direct_product_eq_map U V hUV C sf hU hV dm μm
  have hcorepos (x : U) (hx : x.val ∈ core) : 0 < dd.eigenvector x := by
    exact mul_pos (inv_pos.mpr d.rate_pos) (positive ⟨x.val, hUV x.property⟩ hx)
  refine ⟨ν, ?_, ?_, ?_, ?_⟩
  · change (eigenvectorMeasure μd dd.eigenvector).map (Subtype.val : U → X) = _
    rw [hproduct, Measure.map_map measurable_subtype_coe (flatten U V hUV).measurable]
    have he : (Subtype.val : U → X) ∘ flatten U V hUV =
        (Subtype.val : V → X) ∘ (Subtype.val : innerLevel U V → V) := rfl
    rw [he, ← Measure.map_map measurable_subtype_coe measurable_subtype_coe,
      ConullStratumProduct.map_stratum_product_eq_closed_product CV sfV
        (innerLevel U V) hmU hzero d μ mean]
  · exact QuasiErgodic.eigenvectorMeasure_isQuasiErgodic_of_strongFeller (chain C U hU)
      (transferOperator (chain C U hU) (strongFeller C sf U hU))
      (transferOperator_apply (chain C U hU) (strongFeller C sf U hU)) dd μd hd hn
      (strongFeller C sf U hU)
  · intro x hx
    have hp := ConullStratumSupport.core_point_mem_stratum_product_support CV sfV
      (innerLevel U V) hmU hzero d μ mean ((flatten U V hUV).symm x)
      (support ⟨x.val, hUV x.property⟩ hx)
    exact direct_product_support U V hUV C sf hU hV dm μm ((flatten U V hUV).symm x) hp
  · intro ζ hζ hsupp
    have hc : ({x : U | x.val ∈ core} : Set U).Nonempty := by
      obtain ⟨x, hx⟩ := nonempty
      exact ⟨⟨x, coreU hx⟩, hx⟩
    exact QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support (chain C U hU)
      (transferOperator (chain C U hU) (strongFeller C sf U hU))
      (transferOperator_apply (chain C U hU) (strongFeller C sf U hU)) dd μd hd hn
      {x : U | x.val ∈ core} hc hcorepos ζ hζ hsupp
end ConditionedStochasticStabilityHyperbolic.Global.FlattenedConullLocalQuasiErgodic
