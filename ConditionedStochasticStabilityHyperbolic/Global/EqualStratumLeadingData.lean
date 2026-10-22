module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedProductCoordinates

/-! # Proof-preserving identification of equal measurable stratum subtypes

These are equality transports for explicitly proved set/operator identities.
They introduce no spectral or probabilistic assumptions and retain vectors,
representing measures, products and support exactly.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.EqualStratumLeadingData
open ComplexStrongFeller RestrictedLayerChain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def operatorData {P Q : E →L[ℝ] E} {one : E} (h : P = Q)
    (d : RankOneSpectralData P one) : RankOneSpectralData Q one := h ▸ d

theorem operatorData_rate {P Q : E →L[ℝ] E} {one : E} (h : P = Q)
    (d : RankOneSpectralData P one) : (operatorData h d).rate = d.rate := by cases h; rfl

theorem operatorData_vector {P Q : E →L[ℝ] E} {one : E} (h : P = Q)
    (d : RankOneSpectralData P one) : (operatorData h d).eigenvector = d.eigenvector := by cases h; rfl

theorem operatorData_mean {P Q : E →L[ℝ] E} {one : E} (h : P = Q)
    (d : RankOneSpectralData P one) : (operatorData h d).mean = d.mean := by cases h; rfl

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V) (heq : U = V)

local notation "PU" => transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU)
local notation "PV" => transferOperator (𝕜 := ℝ) (chain C V hV) (strongFeller C hSF V hV)

def setData (d : RankOneSpectralData PU (1 : U →ᵇ ℝ)) : RankOneSpectralData PV (1 : V →ᵇ ℝ) := by
  subst V
  exact d

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] in
def setPoint (x : U) : V := ⟨x.val, heq ▸ x.property⟩

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
def setMeasure (K L : Set X) (h : K = L) (μ : Measure K) : Measure L := h ▸ μ

theorem setData_rate (d : RankOneSpectralData PU (1 : U →ᵇ ℝ)) :
    (setData C hSF U V hU hV heq d).rate = d.rate := by subst V; rfl

theorem setData_vector (d : RankOneSpectralData PU (1 : U →ᵇ ℝ)) (x : U) :
    (setData C hSF U V hU hV heq d).eigenvector (setPoint U V heq x) = d.eigenvector x := by subst V; rfl

include hU hV in
theorem setData_represents (d : RankOneSpectralData PU (1 : U →ᵇ ℝ)) (μ : Measure U)
    (hm : ∀ f : U →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) :
    ∀ f : V →ᵇ ℝ, (setData C hSF U V hU hV heq d).mean f = ∫ y, f y ∂setMeasure U V heq μ := by
  subst V
  exact hm

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
theorem setMeasure_finite (μ : Measure U) [IsFiniteMeasure μ] : IsFiniteMeasure (setMeasure U V heq μ) := by
  subst V
  change IsFiniteMeasure μ
  infer_instance

theorem set_product_map (d : RankOneSpectralData PU (1 : U →ᵇ ℝ)) (μ : Measure U) :
    (LeanShared.eigenvectorMeasure (setMeasure U V heq μ)
      (setData C hSF U V hU hV heq d).eigenvector).map Subtype.val =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map (Subtype.val : U → X) := by
  subst V
  rfl

theorem set_product_support (d : RankOneSpectralData PU (1 : U →ᵇ ℝ)) (μ : Measure U) (x : U)
    (hx : x ∈ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    setPoint U V heq x ∈ (LeanShared.eigenvectorMeasure (setMeasure U V heq μ)
      (setData C hSF U V hU hV heq d).eigenvector).support := by
  subst V
  exact hx

end ConditionedStochasticStabilityHyperbolic.Global.EqualStratumLeadingData
