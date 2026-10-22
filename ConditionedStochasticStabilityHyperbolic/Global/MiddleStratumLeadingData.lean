module

public import ConditionedStochasticStabilityHyperbolic.Global.EqualStratumLeadingData

/-!
# Actual middle-stratum sources for a selected prefix diagonal

Direct actual Si=M_d minus M_(d-1) leading data are re-nested inside M_d.
The proved equality of measurable strata identifies this with the upper
block diagonal. Rate, eigenfunction, representing measure and core support
are constructed in the exact types consumed by selected global assembly.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.MiddleStratumLeadingData
open ComplexStrongFeller LayerOperators RestrictedLayerChain NestedLayerKernel
open NestedLeadingData NestedProductCoordinates EqualStratumLeadingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L0 L1 : Set X) (hL0 : MeasurableSet L0) (hL1 : MeasurableSet L1)
local notation "S" => (L1 \ L0)
local notation "hs" => hL1.diff hL0
local notation "A0" => innerLevel L0 L1
local notation "ha0" => hL0.preimage measurable_subtype_coe
local notation "B" => innerLevel S L1
local notation "hb" => MeasurableSet.preimage (MeasurableSet.diff hL1 hL0) measurable_subtype_coe
local notation "C1" => chain C L1 hL1
local notation "sf1" => strongFeller C hSF L1 hL1
local notation "P" => transferOperator (𝕜 := ℝ) (chain C S hs) (strongFeller C hSF S hs)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem middleSetEq : B = A0ᶜ := by
  ext x
  simp only [innerLevel, mem_preimage, mem_sdiff, mem_compl_iff, x.property, true_and]

theorem diagonalEq : transferOperator (𝕜 := ℝ) (chain C1 A0ᶜ (ha0).compl)
    (strongFeller C1 sf1 A0ᶜ (ha0).compl) = upperOperator (𝕜 := ℝ) C1 sf1 A0 ha0 :=
  transferOperator_eq_lower C1 sf1 A0ᶜ (ha0).compl

def middleData (d : RankOneSpectralData P (1 : (S : Set X) →ᵇ ℝ)) :
    RankOneSpectralData (upperOperator (𝕜 := ℝ) C1 sf1 A0 ha0) (1 : (A0ᶜ : Set L1) →ᵇ ℝ) :=
  operatorData (diagonalEq C hSF L0 L1 hL0 hL1)
    (setData C1 sf1 B A0ᶜ hb (ha0).compl (middleSetEq L0 L1)
      (nestedData S L1 sdiff_subset C hSF hs hL1 d))

omit C hSF hL0 hL1 [MeasurableSpace X] [BorelSpace X] [MetricSpace X] in
def middlePoint (x : (S : Set X)) : (A0ᶜ : Set L1) :=
  setPoint B A0ᶜ (middleSetEq L0 L1) ⟨⟨x.val, x.property.1⟩, x.property⟩

omit C hSF [MetricSpace X] [BorelSpace X] in
def middleMeasure (μ : Measure (S : Set X)) : Measure (A0ᶜ : Set L1) :=
  setMeasure B A0ᶜ (middleSetEq L0 L1) (μ.map (flatten S L1 sdiff_subset).symm)

theorem middleData_rate (d : RankOneSpectralData P (1 : (S : Set X) →ᵇ ℝ)) :
    (middleData C hSF L0 L1 hL0 hL1 d).rate = d.rate := by
  let dn := nestedData S L1 sdiff_subset C hSF hs hL1 d
  let ds := setData C1 sf1 B A0ᶜ hb (ha0).compl (middleSetEq L0 L1) dn
  exact (operatorData_rate (diagonalEq C hSF L0 L1 hL0 hL1) ds).trans
    ((setData_rate C1 sf1 B A0ᶜ hb (ha0).compl (middleSetEq L0 L1) dn).trans
      (nestedData_rate S L1 sdiff_subset C hSF hs hL1 d))

theorem middleData_vector (d : RankOneSpectralData P (1 : (S : Set X) →ᵇ ℝ)) (x : (S : Set X)) :
    (middleData C hSF L0 L1 hL0 hL1 d).eigenvector (middlePoint L0 L1 x) = d.eigenvector x := by
  let dn := nestedData S L1 sdiff_subset C hSF hs hL1 d
  let ds := setData C1 sf1 B A0ᶜ hb (ha0).compl (middleSetEq L0 L1) dn
  have ho := congrArg (fun f : (A0ᶜ : Set L1) →ᵇ ℝ => f (middlePoint L0 L1 x))
    (operatorData_vector (diagonalEq C hSF L0 L1 hL0 hL1) ds)
  have he := setData_vector C1 sf1 B A0ᶜ hb (ha0).compl (middleSetEq L0 L1) dn
    ((flatten S L1 sdiff_subset).symm x)
  exact ho.trans (he.trans (by rfl))

/-- Direct actual-stratum left measure gives the exact dominant-diagonal
left measure, without a new representation premise. -/
theorem middleData_represents (d : RankOneSpectralData P (1 : (S : Set X) →ᵇ ℝ))
    (μ : Measure (S : Set X)) (hm : ∀ f : (S : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) (f : (A0ᶜ : Set L1) →ᵇ ℝ) :
    (middleData C hSF L0 L1 hL0 hL1 d).mean f = ∫ y, f y ∂middleMeasure L0 L1 μ := by
  rw [middleData, operatorData_mean]
  exact setData_represents C1 sf1 B A0ᶜ hb (ha0).compl (middleSetEq L0 L1)
    (nestedData S L1 sdiff_subset C hSF hs hL1 d)
    (μ.map (flatten S L1 sdiff_subset).symm)
    (nestedData_represents S L1 sdiff_subset C hSF hs hL1 d μ hm) f

omit C hSF hL0 hL1 [MetricSpace X] [BorelSpace X] in
theorem middleMeasure_finite (μ : Measure (S : Set X)) [IsFiniteMeasure μ] : IsFiniteMeasure (middleMeasure L0 L1 μ) :=
  setMeasure_finite B A0ᶜ (middleSetEq L0 L1) _

/-- Actual produced core support reaches the selected dominant diagonal. -/
theorem middle_product_support (d : RankOneSpectralData P (1 : (S : Set X) →ᵇ ℝ))
    (μ : Measure (S : Set X)) (x : (S : Set X)) (hx : x ∈ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    middlePoint L0 L1 x ∈ (LeanShared.eigenvectorMeasure (middleMeasure L0 L1 μ)
      (middleData C hSF L0 L1 hL0 hL1 d).eigenvector).support := by
  rw [middleData, operatorData_vector]
  exact set_product_support C1 sf1 B A0ᶜ hb (ha0).compl (middleSetEq L0 L1)
    (nestedData S L1 sdiff_subset C hSF hs hL1 d)
    (μ.map (flatten S L1 sdiff_subset).symm) ((flatten S L1 sdiff_subset).symm x)
    (nested_product_support S L1 sdiff_subset C hSF hs hL1 d μ x hx)

end ConditionedStochasticStabilityHyperbolic.Global.MiddleStratumLeadingData
