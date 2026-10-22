module

public import ConditionedStochasticStabilityHyperbolic.Global.ClosedDominantSource

/-! # The selected dominant product equals its produced closed-local source -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ClosedDominantProduct
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel ClosedDominantSource
open ConullStratumLeadingData ConullStratumProduct NestedDirectLeadingData NestedProductCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L0 L1 : Set X) (hL0 : MeasurableSet L0) (hL1 : MeasurableSet L1)

theorem dominant_product_map_eq_closed
    (hzero : ∀ x : (closure (L1 \ L0) : Set X),
      (chain C (closure (L1 \ L0)) (closureLayer_measurable L0 L1)).killedTransition x
        (innerLevel (L1 \ L0) (closure (L1 \ L0)))ᶜ = 0)
    (d : RankOneSpectralData
      (transferOperator (𝕜 := ℝ) (chain C (closure (L1 \ L0)) (closureLayer_measurable L0 L1))
        (strongFeller C hSF (closure (L1 \ L0)) (closureLayer_measurable L0 L1)))
      (1 : (closure (L1 \ L0) : Set X) →ᵇ ℝ))
    (μ : Measure (closure (L1 \ L0) : Set X)) [IsFiniteMeasure μ]
    (hmean : ∀ f : (closure (L1 \ L0) : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) :
    (LeanShared.eigenvectorMeasure (dominantMeasure C hSF L0 L1 d μ)
      (dominantData C hSF L0 L1 hL0 hL1 hzero d).eigenvector).map
        (fun y : ((innerLevel L0 L1)ᶜ : Set L1) => y.val.val) =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val := by
  let S := L1 \ L0
  let K := closure S
  let hs : MeasurableSet S := hL1.diff hL0
  let hk : MeasurableSet K := closureLayer_measurable L0 L1
  let CK := chain C K hk
  let sfK := strongFeller C hSF K hk
  let U := innerLevel S K
  let hu : MeasurableSet U := hs.preimage measurable_subtype_coe
  let ds := stratumData CK sfK U hu hzero d
  let μs := stratumMeasure CK sfK U d μ
  let νs := LeanShared.eigenvectorMeasure μs ds.eigenvector
  have hn := direct_product_eq_map S K subset_closure C hSF hs hk ds μs
  have hm := map_stratum_product_eq_closed_product CK sfK U hu hzero d μ hmean
  have hnX := congrArg (fun ν : Measure S => ν.map (Subtype.val : S → X)) hn
  have hflat : (νs.map (flatten S K subset_closure)).map (Subtype.val : S → X) =
      νs.map (fun y : U => y.val.val) :=
    Measure.map_map measurable_subtype_coe (flatten S K subset_closure).measurable
  have hmX := congrArg (fun ν : Measure K => ν.map (Subtype.val : K → X)) hm
  have hdouble : (νs.map (Subtype.val : U → K)).map (Subtype.val : K → X) =
      νs.map (fun y : U => y.val.val) :=
    Measure.map_map measurable_subtype_coe measurable_subtype_coe
  calc
    _ = (LeanShared.eigenvectorMeasure (actualStratumMeasure C hSF L0 L1 d μ)
        (actualStratumData C hSF L0 L1 hL0 hL1 hzero d).eigenvector).map Subtype.val :=
      MiddleStratumProduct.middle_product_map_eq_actual_stratum C hSF L0 L1 hL0 hL1
        (actualStratumData C hSF L0 L1 hL0 hL1 hzero d)
        (actualStratumMeasure C hSF L0 L1 d μ)
    _ = νs.map (fun y : U => y.val.val) := hnX.trans hflat
    _ = _ := hdouble.symm.trans hmX

end ConditionedStochasticStabilityHyperbolic.Global.ClosedDominantProduct
