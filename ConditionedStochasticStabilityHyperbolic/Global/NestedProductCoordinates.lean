module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedDirectLeadingData
public import LeanShared.Probability.EigenvectorMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Actual product probabilities and core support under nested coordinates

Both directions of actual kernel flattening preserve the constructed product
measure exactly. Homeomorphism coordinates transport core support as well;
no new local support or physical weak-limit assumption is introduced.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.NestedProductCoordinates
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel NestedLeadingData NestedDirectLeadingData

private theorem product_map_equiv {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (e : Y ≃ᵐ Z) (μ : Measure Y) (g : Y → ℝ) (hg : Measurable g) :
    LeanShared.eigenvectorMeasure (μ.map e) (fun z => g (e.symm z)) =
      (LeanShared.eigenvectorMeasure μ g).map e := by
  unfold LeanShared.eigenvectorMeasure
  ext S hS
  rw [withDensity_apply _ hS, Measure.map_apply e.measurable hS,
    withDensity_apply _ (hS.preimage e.measurable)]
  have he := setLIntegral_map (μ := μ) hS (hg.comp e.symm.measurable).ennreal_ofReal e.measurable
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using he

private theorem support_map_continuous {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [MeasurableSpace Y] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (f : Y → Z) (hf : Measurable f) (hc : Continuous f) (μ : Measure Y)
    (x : Y) (hx : x ∈ μ.support) : f x ∈ (μ.map f).support := by
  rw [Measure.support_eq_forall_isOpen] at hx ⊢
  intro V hxV hV
  rw [Measure.map_apply hf hV.measurableSet]
  exact hx (f ⁻¹' V) hxV (hV.preimage hc)

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (U V : Set X) (hUV : U ⊆ V)
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (hU : MeasurableSet U) (hV : MeasurableSet V)
local notation "Q" => transferOperator (𝕜 := ℝ)
  (chain (chain C V hV) (innerLevel U V) (hU.preimage measurable_subtype_coe))
  (strongFeller (chain C V hV) (strongFeller C hSF V hV) (innerLevel U V) (hU.preimage measurable_subtype_coe))
local notation "P" => transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU)

/-- Forward actual nested-data product is the exact coordinate pushforward. -/
theorem nested_product_eq_map
    (d : RankOneSpectralData P (1 : U →ᵇ ℝ)) (μ : Measure U) :
    LeanShared.eigenvectorMeasure (μ.map (flatten U V hUV).symm)
      (nestedData U V hUV C hSF hU hV d).eigenvector =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map (flatten U V hUV).symm :=
  product_map_equiv (flatten U V hUV).symm μ d.eigenvector d.eigenvector.continuous.measurable

/-- Inverse actual nested-data product is the exact coordinate pushforward. -/
theorem direct_product_eq_map
    (d : RankOneSpectralData Q (1 : innerLevel U V →ᵇ ℝ)) (μ : Measure (innerLevel U V)) :
    LeanShared.eigenvectorMeasure (μ.map (flatten U V hUV))
      (directData U V hUV C hSF hU hV d).eigenvector =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map (flatten U V hUV) :=
  product_map_equiv (flatten U V hUV) μ d.eigenvector d.eigenvector.continuous.measurable

/-- Produced actual stratum core support passes to its nested dominant
prefix coordinates. -/
theorem nested_product_support
    (d : RankOneSpectralData P (1 : U →ᵇ ℝ)) (μ : Measure U) (x : U)
    (hx : x ∈ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    (flatten U V hUV).symm x ∈
      (LeanShared.eigenvectorMeasure (μ.map (flatten U V hUV).symm)
        (nestedData U V hUV C hSF hU hV d).eigenvector).support := by
  rw [nested_product_eq_map U V hUV C hSF hU hV d μ]
  exact support_map_continuous (flatten U V hUV).symm (flatten U V hUV).symm.measurable
    (flattenHomeomorph U V hUV).symm.continuous _ x hx

/-- Produced closed conull-stratum core support passes to direct actual
ambient-stratum coordinates. -/
theorem direct_product_support
    (d : RankOneSpectralData Q (1 : innerLevel U V →ᵇ ℝ))
    (μ : Measure (innerLevel U V)) (x : innerLevel U V)
    (hx : x ∈ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    flatten U V hUV x ∈
      (LeanShared.eigenvectorMeasure (μ.map (flatten U V hUV))
        (directData U V hUV C hSF hU hV d).eigenvector).support := by
  rw [direct_product_eq_map U V hUV C hSF hU hV d μ]
  exact support_map_continuous (flatten U V hUV) (flatten U V hUV).measurable
    (flattenHomeomorph U V hUV).continuous _ x hx

end ConditionedStochasticStabilityHyperbolic.Global.NestedProductCoordinates
