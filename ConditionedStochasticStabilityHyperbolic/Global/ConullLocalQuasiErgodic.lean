module
public import ConditionedStochasticStabilityHyperbolic.Global.ConullStratumSupport
public import ConditionedStochasticStabilityHyperbolic.Spectral.QuasiErgodic

/-! The same produced closed-local probability is the unique qualified
local QEM on the literal stratum after deleting a transition-null boundary.
The stratum need not be compact; its left measure is constructed from the
closed one instead of postulating a new Riesz representation. -/
public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ConullLocalQuasiErgodic
open LeanShared ComplexStrongFeller ConullStratumLeadingData

/-- Actual conull restriction preserves the same physical probability,
its core support, and the manuscript's qualified local uniqueness. -/
theorem exists_stratum_QEM
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)
    (U : Set X) (hU : MeasurableSet U)
    (hzero : ∀ x, C.killedTransition x Uᶜ = 0)
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C sf) (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (mean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)
    (nonneg : ∀ x, 0 ≤ d.eigenvector x)
    (core : Set X) (nonempty : core.Nonempty) (coreU : core ⊆ U)
    (positive : ∀ x ∈ core, 0 < d.eigenvector x)
    (support : core ⊆ (eigenvectorMeasure μ d.eigenvector).support) :
    ∃ ν : ProbabilityMeasure U,
      (ν : Measure U).map Subtype.val = eigenvectorMeasure μ d.eigenvector ∧
      (RestrictedLayerChain.chain C U hU).IsQuasiErgodic (ν : Measure U) ∧
      {x : U | x.val ∈ core} ⊆ (ν : Measure U).support ∧
      ∀ ζ : Measure U, (RestrictedLayerChain.chain C U hU).IsQuasiErgodic ζ →
        {x : U | x.val ∈ core} ⊆ ζ.support → ζ = (ν : Measure U) := by
  let D := RestrictedLayerChain.chain C U hU
  let sfD := RestrictedLayerChain.strongFeller C sf U hU
  let dm := stratumData C sf U hU hzero d
  let μm := stratumMeasure C sf U d μ
  let : IsFiniteMeasure μm := stratumMeasure_finite C sf U hU d μ
  have hm : ∀ f, dm.mean f = ∫ x, f x ∂μm :=
    stratumMeasure_represents C sf U hU hzero d μ mean
  have hn : ∀ x, 0 ≤ dm.eigenvector x := by
    intro x
    exact mul_nonneg (inv_nonneg.mpr d.rate_pos.le) (nonneg x.val)
  have : IsProbabilityMeasure (eigenvectorMeasure μm dm.eigenvector) :=
    eigenvector_product_isProbability dm μm hm hn
  let ν : ProbabilityMeasure U := ⟨eigenvectorMeasure μm dm.eigenvector, inferInstance⟩
  refine ⟨ν, ?_, ?_, ?_, ?_⟩
  · exact ConullStratumProduct.map_stratum_product_eq_closed_product C sf U hU hzero d μ mean
  · exact QuasiErgodic.eigenvectorMeasure_isQuasiErgodic_of_strongFeller D
      (transferOperator D sfD) (transferOperator_apply D sfD) dm μm hm hn sfD
  · intro x hx
    exact ConullStratumSupport.core_point_mem_stratum_product_support C sf U hU hzero
      d μ mean x (support hx)
  · intro ζ hζ hsupp
    have hc : ({x : U | x.val ∈ core} : Set U).Nonempty := by
      obtain ⟨x, hx⟩ := nonempty
      exact ⟨⟨x, coreU hx⟩, hx⟩
    exact QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support D
      (transferOperator D sfD) (transferOperator_apply D sfD) dm μm hm hn
      {x : U | x.val ∈ core} hc
      (fun x hx => stratumData_vector_pos C sf U hU hzero d x (positive x.val hx)) ζ hζ hsupp
end ConditionedStochasticStabilityHyperbolic.Global.ConullLocalQuasiErgodic
