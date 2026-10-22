module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedLayerKernel
public import ConditionedStochasticStabilityHyperbolic.Global.LayerNormalizedGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.HomeomorphicEigenproduct

/-! Flattening actual nested restrictions preserves the produced rank-one
gap and exactly pushes its probability product to the direct live subtype. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.NestedNormalizedGap
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
    (transferOperator (𝕜 := ℝ) CI sI).comp
      (HomeomorphicGapTransport.pull ⟨flattenHomeomorph U P hUP,
        (flattenHomeomorph U P hUP).continuous⟩) =
    (HomeomorphicGapTransport.pull ⟨flattenHomeomorph U P hUP,
      (flattenHomeomorph U P hUP).continuous⟩).comp (transferOperator (𝕜 := ℝ) CD sD) := by
  ext f x
  change transferOperator (𝕜 := ℝ) CI sI (pullback U P hUP f) x =
    pullback U P hUP (transferOperator (𝕜 := ℝ) CD sD f) x
  exact congrArg (fun v : innerLevel U P →ᵇ ℝ => v x)
    (transfer_nested_pullback U P hUP C sf hU hP f)

/-- The literal direct restriction receives the actual nested spectral data. -/
def data (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CI sI)
    (1 : innerLevel U P →ᵇ ℝ)) :
    RankOneSpectralData (transferOperator (𝕜 := ℝ) CD sD) (1 : U →ᵇ ℝ) :=
  HomeomorphicGapTransport.transport (flattenHomeomorph U P hUP).symm _ _ d
    (intertwines U P hUP C sf hU hP)

@[simp] theorem data_vector
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CI sI) (1 : innerLevel U P →ᵇ ℝ))
    (x : U) :
    (data U P hUP C sf hU hP d).eigenvector x =
      d.eigenvector ((flattenHomeomorph U P hUP).symm x) := rfl

variable [CompactSpace U] [CompactSpace (innerLevel U P)]

 theorem product_map
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CI sI) (1 : innerLevel U P →ᵇ ℝ)) :
    productMeasure CD sD (data U P hUP C sf hU hP d) =
      (productMeasure CI sI d).map (flattenHomeomorph U P hUP) :=
  HomeomorphicGapTransport.transport_eigenproduct (flattenHomeomorph U P hUP).symm _ _ d
    (intertwines U P hUP C sf hU hP)
    (LayerRankOne.actual_transfer_positive CD sD)
    (LayerRankOne.actual_transfer_positive CI sI)

/-- The local gap uses exactly the pushed existing product probability. -/
theorem normalizedGap
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CI sI) (1 : innerLevel U P →ᵇ ℝ))
    (core : Set U)
    (positive : ∀ x ∈ core, 0 < d.eigenvector ((flattenHomeomorph U P hUP).symm x)) :
    Paper.LocalConclusions.NormalizedGap CD core
      (LayerNormalizedGap.probability CD sD (data U P hUP C sf hU hP d)) ∧
    ((LayerNormalizedGap.probability CD sD (data U P hUP C sf hU hP d) : ProbabilityMeasure U) : Measure U) =
      (productMeasure CI sI d).map (flattenHomeomorph U P hUP) := by
  refine ⟨LayerNormalizedGap.normalizedGap CD sD _ core ?_, product_map U P hUP C sf hU hP d⟩
  simpa only [data_vector] using positive

end ConditionedStochasticStabilityHyperbolic.Global.NestedNormalizedGap
