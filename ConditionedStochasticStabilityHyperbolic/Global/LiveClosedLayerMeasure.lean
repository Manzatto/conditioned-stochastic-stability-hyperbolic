module

public import ConditionedStochasticStabilityHyperbolic.Global.LiveClosedLayerSource
public import ConditionedStochasticStabilityHyperbolic.Global.NestedProductCoordinates

/-! # The literal live closed layer has the original physical product -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.LiveClosedLayerMeasure
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel NestedLeadingData
open EqualStratumLeadingData NestedProductCoordinates LiveClosedLayerSource
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V)
  (hKV : closure U ⊆ V)
  (d : RankOneSpectralData (transferOperator (𝕜 := ℝ)
    (chain C (closure U) isClosed_closure.measurableSet)
    (strongFeller C hSF (closure U) isClosed_closure.measurableSet))
    (1 : (closure U : Set X) →ᵇ ℝ))

variable (μ : Measure (closure U : Set X))

def liveClosedMeasure : Measure (closure (innerLevel U V)) :=
  setMeasure (innerLevel (closure U) V) (closure (innerLevel U V))
    (closure_live_stratum U V (subset_closure.trans hKV)).symm
    (μ.map (flatten (closure U) V hKV).symm)

include hV in
theorem liveClosedMeasure_represents
    (hmean : ∀ f : (closure U : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) :
    ∀ f : (closure (innerLevel U V)) →ᵇ ℝ,
      (liveClosedData C hSF U V hV hKV d).mean f =
        ∫ y, f y ∂liveClosedMeasure U V hKV μ :=
  setData_represents (chain C V hV) (strongFeller C hSF V hV)
    (innerLevel (closure U) V) (closure (innerLevel U V))
    (isClosed_closure.measurableSet.preimage measurable_subtype_coe) isClosed_closure.measurableSet
    (closure_live_stratum U V (subset_closure.trans hKV)).symm
    (nestedData (closure U) V hKV C hSF isClosed_closure.measurableSet hV d)
    (μ.map (flatten (closure U) V hKV).symm)
    (nestedData_represents (closure U) V hKV C hSF isClosed_closure.measurableSet hV d μ hmean)

omit [BorelSpace X] in
theorem liveClosedMeasure_finite [IsFiniteMeasure μ] :
    IsFiniteMeasure (liveClosedMeasure U V hKV μ) :=
  setMeasure_finite (innerLevel (closure U) V) (closure (innerLevel U V))
    (closure_live_stratum U V (subset_closure.trans hKV)).symm _

include hV in
theorem liveClosedProduct_map_eq_ambient :
    (LeanShared.eigenvectorMeasure (liveClosedMeasure U V hKV μ)
      (liveClosedData C hSF U V hV hKV d).eigenvector).map
        (fun y : (closure (innerLevel U V)) => y.val.val) =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val := by
  let K := closure U
  let E := innerLevel K V
  let B := closure (innerLevel U V)
  let he : E = B := (closure_live_stratum U V (subset_closure.trans hKV)).symm
  let dn := nestedData K V hKV C hSF isClosed_closure.measurableSet hV d
  let μn := μ.map (flatten K V hKV).symm
  let νn := LeanShared.eigenvectorMeasure μn dn.eigenvector
  have heq := set_product_map (chain C V hV) (strongFeller C hSF V hV) E B
    (isClosed_closure.measurableSet.preimage measurable_subtype_coe) isClosed_closure.measurableSet he dn μn
  have heqX := congrArg (fun ν : Measure V => ν.map (Subtype.val : V → X)) heq
  have hn := nested_product_eq_map K V hKV C hSF isClosed_closure.measurableSet hV d μ
  have hleft : ((LeanShared.eigenvectorMeasure (liveClosedMeasure U V hKV μ)
      (liveClosedData C hSF U V hV hKV d).eigenvector).map
        (Subtype.val : B → V)).map (Subtype.val : V → X) =
      (LeanShared.eigenvectorMeasure (liveClosedMeasure U V hKV μ)
      (liveClosedData C hSF U V hV hKV d).eigenvector).map (fun y => y.val.val) :=
    Measure.map_map measurable_subtype_coe measurable_subtype_coe
  have hright : (νn.map (Subtype.val : E → V)).map (Subtype.val : V → X) =
      νn.map (fun y : E => y.val.val) :=
    Measure.map_map measurable_subtype_coe measurable_subtype_coe
  have hf : ((LeanShared.eigenvectorMeasure μ d.eigenvector).map (flatten K V hKV).symm).map
      (fun y : E => y.val.val) = (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val :=
    Measure.map_map (measurable_subtype_coe.comp measurable_subtype_coe)
      (flatten K V hKV).symm.measurable
  calc
    _ = νn.map (fun y : E => y.val.val) := hleft.symm.trans (heqX.trans hright)
    _ = ((LeanShared.eigenvectorMeasure μ d.eigenvector).map (flatten K V hKV).symm).map
        (fun y : E => y.val.val) := congrArg (fun ν => ν.map (fun y : E => y.val.val)) hn
    _ = _ := hf

/-- The actual ambient closed point in literal live-closure coordinates. -/
def liveClosedPoint (p : (closure U : Set X)) : closure (innerLevel U V) :=
  setPoint (innerLevel (closure U) V) (closure (innerLevel U V))
    (closure_live_stratum U V (subset_closure.trans hKV)).symm
    ((flatten (closure U) V hKV).symm p)

include hV in
theorem liveClosedData_vector (p : (closure U : Set X)) :
    (liveClosedData C hSF U V hV hKV d).eigenvector (liveClosedPoint U V hKV p) =
      d.eigenvector p := by
  have he := setData_vector (chain C V hV) (strongFeller C hSF V hV)
    (innerLevel (closure U) V) (closure (innerLevel U V))
    (isClosed_closure.measurableSet.preimage measurable_subtype_coe) isClosed_closure.measurableSet
    (closure_live_stratum U V (subset_closure.trans hKV)).symm
    (nestedData (closure U) V hKV C hSF isClosed_closure.measurableSet hV d)
    ((flatten (closure U) V hKV).symm p)
  exact he.trans (congrArg d.eigenvector (MeasurableEquiv.apply_symm_apply _ p))

include hV in
theorem liveClosedProduct_core_support (p : (closure U : Set X))
    (hp : p ∈ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    liveClosedPoint U V hKV p ∈ (LeanShared.eigenvectorMeasure (liveClosedMeasure U V hKV μ)
      (liveClosedData C hSF U V hV hKV d).eigenvector).support := by
  have hn := nested_product_support (closure U) V hKV C hSF isClosed_closure.measurableSet hV d μ p hp
  exact set_product_support (chain C V hV) (strongFeller C hSF V hV)
    (innerLevel (closure U) V) (closure (innerLevel U V))
    (isClosed_closure.measurableSet.preimage measurable_subtype_coe) isClosed_closure.measurableSet
    (closure_live_stratum U V (subset_closure.trans hKV)).symm
    (nestedData (closure U) V hKV C hSF isClosed_closure.measurableSet hV d)
    (μ.map (flatten (closure U) V hKV).symm) _ hn

end ConditionedStochasticStabilityHyperbolic.Global.LiveClosedLayerMeasure
