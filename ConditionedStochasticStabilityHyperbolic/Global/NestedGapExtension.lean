module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedNormalizedGap

/-! The inverse of actual nested-state flattening, needed to extend a
produced literal live-prefix gap back to its ambient compact prefix. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.NestedGapExtension
open LeanShared NestedLayerKernel ComplexStrongFeller LayerQuasiErgodic
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (U P : Set X) (hUP : U ⊆ P)
  (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)
  (hU : MeasurableSet U) (hP : MeasurableSet P)
local notation "CI" => RestrictedLayerChain.chain (RestrictedLayerChain.chain C P hP)
  (innerLevel U P) (hU.preimage measurable_subtype_coe)
local notation "sI" => RestrictedLayerChain.strongFeller (RestrictedLayerChain.chain C P hP)
  (RestrictedLayerChain.strongFeller C sf P hP) (innerLevel U P) (hU.preimage measurable_subtype_coe)
local notation "CD" => RestrictedLayerChain.chain C U hU
local notation "sD" => RestrictedLayerChain.strongFeller C sf U hU

 theorem intertwines :
    (transferOperator (𝕜 := ℝ) CD sD).comp
      (HomeomorphicGapTransport.pull ⟨(flattenHomeomorph U P hUP).symm,
        (flattenHomeomorph U P hUP).symm.continuous⟩) =
    (HomeomorphicGapTransport.pull ⟨(flattenHomeomorph U P hUP).symm,
      (flattenHomeomorph U P hUP).symm.continuous⟩).comp (transferOperator (𝕜 := ℝ) CI sI) := by
  apply HomeomorphicGapTransport.intertwining (flattenHomeomorph U P hUP)
    (CI).killedTransition (CD).killedTransition _ _
    (transferOperator_apply CI sI) (transferOperator_apply CD sD)
  intro x
  have actual := congrArg (fun K => K x) (map_nested_killedTransition U P hUP C hU hP)
  rw [ProbabilityTheory.Kernel.map_apply _ (flatten U P hUP).measurable,
    ProbabilityTheory.Kernel.comap_apply] at actual
  exact actual

/-- Construct nested coordinates from the already produced direct gap. -/
def data (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CD sD) (1 : U →ᵇ ℝ)) :
    RankOneSpectralData (transferOperator (𝕜 := ℝ) CI sI) (1 : innerLevel U P →ᵇ ℝ) :=
  HomeomorphicGapTransport.transport (flattenHomeomorph U P hUP) _ _ d
    (intertwines U P hUP C sf hU hP)

@[simp] theorem data_vector
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CD sD) (1 : U →ᵇ ℝ))
    (x : innerLevel U P) :
    (data U P hUP C sf hU hP d).eigenvector x = d.eigenvector (flatten U P hUP x) := rfl

variable [CompactSpace U] [CompactSpace (innerLevel U P)]

 theorem product_map
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CD sD) (1 : U →ᵇ ℝ)) :
    (productMeasure CI sI (data U P hUP C sf hU hP d)).map (flattenHomeomorph U P hUP) =
      productMeasure CD sD d := by
  have h := HomeomorphicGapTransport.transport_eigenproduct (flattenHomeomorph U P hUP) _ _ d
    (intertwines U P hUP C sf hU hP)
    (LayerRankOne.actual_transfer_positive CI sI) (LayerRankOne.actual_transfer_positive CD sD)
  have actual : productMeasure CI sI (data U P hUP C sf hU hP d) =
      (productMeasure CD sD d).map (flattenHomeomorph U P hUP).symm := h
  rw [actual, Measure.map_map (flattenHomeomorph U P hUP).measurable
    (flattenHomeomorph U P hUP).symm.measurable]
  simp only [Function.comp_def, Homeomorph.apply_symm_apply]
  exact Measure.map_id

end ConditionedStochasticStabilityHyperbolic.Global.NestedGapExtension
