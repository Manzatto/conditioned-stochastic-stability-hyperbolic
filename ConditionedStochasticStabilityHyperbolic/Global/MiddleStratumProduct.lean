module

public import ConditionedStochasticStabilityHyperbolic.Global.MiddleStratumLeadingData

/-! # Middle dominant coordinates preserve the actual physical product

The equal-set and nested-coordinate constructions leave the product measure
unchanged after ambient inclusion. Thus the actual selected QEM assembly
inherits the produced closed-local physical probability and its weak limit.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.MiddleStratumProduct
open ComplexStrongFeller LayerOperators RestrictedLayerChain NestedLayerKernel
open NestedLeadingData NestedProductCoordinates EqualStratumLeadingData MiddleStratumLeadingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L0 L1 : Set X) (hL0 : MeasurableSet L0) (hL1 : MeasurableSet L1)

/-- The actual dominant diagonal product pushed to the manifold is exactly
the direct actual-stratum physical product pushed to the same manifold. -/
theorem middle_product_map_eq_actual_stratum
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (chain C (L1 \ L0) (hL1.diff hL0)) (strongFeller C hSF (L1 \ L0) (hL1.diff hL0)))
      (1 : (L1 \ L0 : Set X) →ᵇ ℝ)) (μ : Measure (L1 \ L0 : Set X)) :
    (LeanShared.eigenvectorMeasure (middleMeasure L0 L1 μ)
      (middleData C hSF L0 L1 hL0 hL1 d).eigenvector).map
        (fun y : ((innerLevel L0 L1)ᶜ : Set L1) => y.val.val) =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val := by
  let S := L1 \ L0
  let B := innerLevel S L1
  let A0 := innerLevel L0 L1
  let hb : MeasurableSet B := (hL1.diff hL0).preimage measurable_subtype_coe
  let ha : MeasurableSet A0 := hL0.preimage measurable_subtype_coe
  let C1 := chain C L1 hL1
  let sf1 := strongFeller C hSF L1 hL1
  let dn := nestedData S L1 sdiff_subset C hSF (hL1.diff hL0) hL1 d
  let μn := μ.map (flatten S L1 sdiff_subset).symm
  let ds := setData C1 sf1 B A0ᶜ hb ha.compl (middleSetEq L0 L1) dn
  let νmid := LeanShared.eigenvectorMeasure (middleMeasure L0 L1 μ)
    (middleData C hSF L0 L1 hL0 hL1 d).eigenvector
  let νset := LeanShared.eigenvectorMeasure (middleMeasure L0 L1 μ) ds.eigenvector
  let νnest := LeanShared.eigenvectorMeasure μn dn.eigenvector
  let νsrc := LeanShared.eigenvectorMeasure μ d.eigenvector
  have hcast : νmid = νset := congrArg
    (fun g : (A0ᶜ : Set L1) →ᵇ ℝ => LeanShared.eigenvectorMeasure (middleMeasure L0 L1 μ) g)
    (operatorData_vector (diagonalEq C hSF L0 L1 hL0 hL1) ds)
  have hs : νset.map (Subtype.val : (A0ᶜ : Set L1) → L1) =
      νnest.map (Subtype.val : B → L1) :=
    set_product_map C1 sf1 B A0ᶜ hb ha.compl (middleSetEq L0 L1) dn μn
  have hsX := congrArg (fun ν : Measure L1 => ν.map (Subtype.val : L1 → X)) hs
  have hleft : (νset.map (Subtype.val : (A0ᶜ : Set L1) → L1)).map (Subtype.val : L1 → X) =
      νset.map (fun y => y.val.val) := Measure.map_map measurable_subtype_coe measurable_subtype_coe
  have hright : (νnest.map (Subtype.val : B → L1)).map (Subtype.val : L1 → X) =
      νnest.map (fun y => y.val.val) := Measure.map_map measurable_subtype_coe measurable_subtype_coe
  have hn : νnest = νsrc.map (flatten S L1 sdiff_subset).symm :=
    nested_product_eq_map S L1 sdiff_subset C hSF (hL1.diff hL0) hL1 d μ
  have hf : (νsrc.map (flatten S L1 sdiff_subset).symm).map
      (fun y : B => y.val.val) = νsrc.map (Subtype.val : S → X) := by
    exact Measure.map_map
      (show Measurable (fun y : B => y.val.val) from
        measurable_subtype_coe.comp measurable_subtype_coe)
      (flatten S L1 sdiff_subset).symm.measurable
  calc
    _ = νset.map (fun y => y.val.val) := congrArg (fun ν => ν.map (fun y => y.val.val)) hcast
    _ = νnest.map (fun y => y.val.val) := hleft.symm.trans (hsX.trans hright)
    _ = (νsrc.map (flatten S L1 sdiff_subset).symm).map (fun y => y.val.val) :=
      congrArg (fun ν => ν.map (fun y : B => y.val.val)) hn
    _ = _ := hf

end ConditionedStochasticStabilityHyperbolic.Global.MiddleStratumProduct
