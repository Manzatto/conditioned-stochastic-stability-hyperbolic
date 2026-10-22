module
public import ConditionedStochasticStabilityHyperbolic.Global.FlattenedConullLocalQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.LayerNormalizedGap

/-! A generated closed-local normalized gap supplies all finite left data
for the literal-stratum QEM, retaining the very same physical probability. -/
public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.NormalizedConullLocalQuasiErgodic
open LeanShared ComplexStrongFeller RestrictedLayerChain NestedLayerKernel

theorem exists_direct_stratum_QEM
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)
    (U V : Set X) (hUV : U ⊆ V) (hU : MeasurableSet U) (hV : MeasurableSet V)
    [CompactSpace V]
    (hzero : ∀ x, (chain C V hV).killedTransition x (innerLevel U V)ᶜ = 0)
    (core : Set X) (nonempty : core.Nonempty) (coreU : core ⊆ U)
    (νClosed : ProbabilityMeasure V)
    (gap : Paper.LocalConclusions.NormalizedGap (chain C V hV)
      {x : V | x.val ∈ core} νClosed)
    (support : {x : V | x.val ∈ core} ⊆ (νClosed : Measure V).support) :
    ∃ ν : ProbabilityMeasure U,
      (ν : Measure U).map Subtype.val = (νClosed : Measure V).map Subtype.val ∧
      (chain C U hU).IsQuasiErgodic (ν : Measure U) ∧
      {x : U | x.val ∈ core} ⊆ (ν : Measure U).support ∧
      ∀ ζ : Measure U, (chain C U hU).IsQuasiErgodic ζ →
        {x : U | x.val ∈ core} ⊆ ζ.support → ζ = (ν : Measure U) := by
  obtain ⟨sfLocal, d, product, positive⟩ := gap
  let CV := chain C V hV
  let sfV := strongFeller C sf V hV
  have eq : strongFellerTransferOperator CV sfLocal = transferOperator CV sfV := by
    ext f x
    rw [strongFellerTransferOperator_represents, transferOperator_apply]
  let dd := d.rewriteOperator eq
  let pos : ∀ f : V →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ strongFellerTransferOperator CV sfLocal f x := by
    intro f hf x
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  let μ := d.eigenmeasure pos
  have mean : ∀ f : V →ᵇ ℝ, dd.mean f = ∫ x, f x ∂μ := by
    intro f
    rw [RankOneSpectralData.rewriteOperator_mean]
    exact d.eigenmeasure_represents pos f
  have nonneg : ∀ x, 0 ≤ dd.eigenvector x := by
    rw [RankOneSpectralData.rewriteOperator_vector]
    exact d.eigenvector_nonneg_of_positive pos
  have same : eigenvectorMeasure μ dd.eigenvector = (νClosed : Measure V) := by
    rw [RankOneSpectralData.rewriteOperator_vector]
    exact product.symm
  obtain ⟨ν, pushed, qem, supp, unique⟩ :=
    FlattenedConullLocalQuasiErgodic.exists_direct_stratum_QEM C sf U V hUV hU hV hzero
      dd μ mean nonneg core nonempty coreU
      (by
        intro x hx
        change 0 < (d.rewriteOperator eq).eigenvector x
        rw [RankOneSpectralData.rewriteOperator_vector]
        exact positive x hx)
      (by
        intro x hx
        rw [same]
        exact support hx)
  exact ⟨ν, pushed.trans (congrArg (fun η : Measure V => η.map Subtype.val) same), qem, supp, unique⟩
end ConditionedStochasticStabilityHyperbolic.Global.NormalizedConullLocalQuasiErgodic
