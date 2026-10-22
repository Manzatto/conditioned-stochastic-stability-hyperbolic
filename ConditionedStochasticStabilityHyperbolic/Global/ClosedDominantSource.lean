module

public import ConditionedStochasticStabilityHyperbolic.Global.ConullStratumSupport
public import ConditionedStochasticStabilityHyperbolic.Global.MiddleStratumProduct

/-!
# Produced closed-local sources construct the actual selected middle diagonal

The entire coordinate pipeline is constructed: closed layer, conull actual
stratum, direct ambient stratum, and selected middle diagonal. Closed-local
spectral/measure/core sources suffice; no actual-stratum or block-coordinate
spectral gap, representing measure, or support result is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ClosedDominantSource
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel
open ConullStratumLeadingData ConullStratumSupport ConullStratumProduct
open NestedDirectLeadingData NestedProductCoordinates MiddleStratumLeadingData MiddleStratumProduct
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L0 L1 : Set X) (hL0 : MeasurableSet L0) (hL1 : MeasurableSet L1)
local notation "S" => (L1 \ L0)
local notation "K" => (closure (L1 \ L0))
local notation "hs" => MeasurableSet.diff hL1 hL0
theorem closureLayer_measurable (L0 L1 : Set X) :
    MeasurableSet (closure (L1 \ L0)) := isClosed_closure.measurableSet
local notation "hk" => closureLayer_measurable L0 L1
local notation "UK" => innerLevel S K
local notation "hu" => MeasurableSet.preimage (MeasurableSet.diff hL1 hL0) measurable_subtype_coe
local notation "CK" => chain C K hk
local notation "sfK" => strongFeller C hSF K hk
local notation "PK" => transferOperator (𝕜 := ℝ) (chain C K (closureLayer_measurable L0 L1)) (strongFeller C hSF K (closureLayer_measurable L0 L1))
local notation "A0" => innerLevel L0 L1
local notation "ha" => hL0.preimage measurable_subtype_coe
variable (hzero : ∀ x : (closure (L1 \ L0) : Set X),
    (chain C (closure (L1 \ L0)) (closureLayer_measurable L0 L1)).killedTransition x
      (innerLevel (L1 \ L0) (closure (L1 \ L0)))ᶜ = 0)
  (d : RankOneSpectralData
    (transferOperator (𝕜 := ℝ) (chain C (closure (L1 \ L0)) (closureLayer_measurable L0 L1))
      (strongFeller C hSF (closure (L1 \ L0)) (closureLayer_measurable L0 L1)))
    (1 : (closure (L1 \ L0) : Set X) →ᵇ ℝ))

/-- Direct actual-stratum gap built from the produced closed-local gap. -/
def actualStratumData : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C S hs)
    (strongFeller C hSF S hs)) (1 : (S : Set X) →ᵇ ℝ) :=
  directData S K subset_closure C hSF hs hk
    (ConullStratumLeadingData.stratumData CK sfK UK hu hzero d)

/-- Actual selected middle diagonal gap, with no new spectral hypothesis. -/
def dominantData : RankOneSpectralData (LayerOperators.upperOperator (𝕜 := ℝ)
    (chain C L1 hL1) (strongFeller C hSF L1 hL1) A0 ha) (1 : (A0ᶜ : Set L1) →ᵇ ℝ) :=
  middleData C hSF L0 L1 hL0 hL1 (actualStratumData C hSF L0 L1 hL0 hL1 hzero d)

variable (μ : Measure (closure (L1 \ L0) : Set X)) [IsFiniteMeasure μ]
  (hmean : ∀ f : (closure (L1 \ L0) : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)

def actualStratumMeasure : Measure (S : Set X) :=
  (stratumMeasure CK sfK UK d μ).map (flatten S K subset_closure)

def dominantMeasure : Measure (A0ᶜ : Set L1) :=
  middleMeasure L0 L1 (actualStratumMeasure C hSF L0 L1 d μ)

include hzero hmean in
/-- Actual direct-stratum representing measure is constructed from μ. -/
theorem actualStratum_represents (f : (S : Set X) →ᵇ ℝ) :
    (actualStratumData C hSF L0 L1 hL0 hL1 hzero d).mean f =
      ∫ y, f y ∂actualStratumMeasure C hSF L0 L1 d μ := by
  exact directData_represents S K subset_closure C hSF hs hk
    (ConullStratumLeadingData.stratumData CK sfK UK hu hzero d) (stratumMeasure CK sfK UK d μ)
    (stratumMeasure_represents CK sfK UK hu hzero d μ hmean) f

include hzero hmean in
/-- The final actual middle-diagonal representing measure is produced. -/
theorem dominant_represents (f : (A0ᶜ : Set L1) →ᵇ ℝ) :
    (dominantData C hSF L0 L1 hL0 hL1 hzero d).mean f =
      ∫ y, f y ∂dominantMeasure C hSF L0 L1 d μ :=
  middleData_represents C hSF L0 L1 hL0 hL1
    (actualStratumData C hSF L0 L1 hL0 hL1 hzero d)
    (actualStratumMeasure C hSF L0 L1 d μ)
    (actualStratum_represents C hSF L0 L1 hL0 hL1 hzero d μ hmean) f

include hL0 hL1 in
theorem actualStratumMeasure_finite : IsFiniteMeasure (actualStratumMeasure C hSF L0 L1 d μ) := by
  let : IsFiniteMeasure (stratumMeasure CK sfK UK d μ) := stratumMeasure_finite CK sfK UK hu d μ
  unfold actualStratumMeasure
  infer_instance

include hL0 hL1 in
theorem dominantMeasure_finite : IsFiniteMeasure (dominantMeasure C hSF L0 L1 d μ) := by
  let : IsFiniteMeasure (actualStratumMeasure C hSF L0 L1 d μ) :=
    actualStratumMeasure_finite C hSF L0 L1 hL0 hL1 d μ
  exact middleMeasure_finite L0 L1 _

theorem dominant_rate : (dominantData C hSF L0 L1 hL0 hL1 hzero d).rate = d.rate := by
  exact (middleData_rate C hSF L0 L1 hL0 hL1 (actualStratumData C hSF L0 L1 hL0 hL1 hzero d)).trans rfl

theorem dominant_vector (p : (S : Set X)) :
    (dominantData C hSF L0 L1 hL0 hL1 hzero d).eigenvector (middlePoint L0 L1 p) =
      d.rate⁻¹ * d.eigenvector ⟨p.val, subset_closure p.property⟩ := by
  have he := middleData_vector C hSF L0 L1 hL0 hL1
    (actualStratumData C hSF L0 L1 hL0 hL1 hzero d) p
  exact he

include hzero hmean in
/-- The actual middle-diagonal core support is produced from CLOSED local
core support at the corresponding ambient point. -/
theorem dominant_core_support (p : (S : Set X))
    (hp : (⟨p.val, subset_closure p.property⟩ : (K : Set X)) ∈
      (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    middlePoint L0 L1 p ∈ (LeanShared.eigenvectorMeasure
      (dominantMeasure C hSF L0 L1 d μ)
      (dominantData C hSF L0 L1 hL0 hL1 hzero d).eigenvector).support := by
  have hn := core_point_mem_stratum_product_support CK sfK UK hu hzero d μ hmean
    ((flatten S K subset_closure).symm p) hp
  have hd := direct_product_support S K subset_closure C hSF hs hk
    (ConullStratumLeadingData.stratumData CK sfK UK hu hzero d) (stratumMeasure CK sfK UK d μ)
    ((flatten S K subset_closure).symm p) hn
  rw [MeasurableEquiv.apply_symm_apply] at hd
  exact middle_product_support C hSF L0 L1 hL0 hL1
    (actualStratumData C hSF L0 L1 hL0 hL1 hzero d)
    (actualStratumMeasure C hSF L0 L1 d μ) p hd

end ConditionedStochasticStabilityHyperbolic.Global.ClosedDominantSource
