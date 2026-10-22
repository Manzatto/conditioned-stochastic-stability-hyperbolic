module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedNormalizedGap
public import ConditionedStochasticStabilityHyperbolic.Global.ConullStratumProduct
public import ConditionedStochasticStabilityHyperbolic.Global.LivePrefixGeometry

/-! A produced compact-prefix gap descends to the literal live prefix P\A.
The absorbing target has zero kernel mass. Both the live gap and its exact
ambient product probability are derived, without a new spectral input. -/
@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.LivePrefixNormalizedGap
open LeanShared ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic
open ConullStratumLeadingData ConullStratumProduct NestedLayerKernel

section Conull
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  (C : AbsorbingMarkovChains.CanonicalChain Z) (sf : HasStrongFellerKernel C)
  (U : Set Z) [CompactSpace U] (hU : MeasurableSet U)
  (hz : ∀ x, C.killedTransition x Uᶜ = 0)
  (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C sf) (1 : Z →ᵇ ℝ))

/-- Riesz representation gives the same literal-stratum measure as the
explicit closed-prefix measure construction. -/
theorem conull_product_map :
    (productMeasure (chain C U hU) (strongFeller C sf U hU)
      (stratumData C sf U hU hz d)).map Subtype.val = productMeasure C sf d := by
  let μ := leadingMeasure C sf d
  have hm : ∀ f : Z →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ :=
    d.eigenmeasure_represents (LayerRankOne.actual_transfer_positive C sf)
  let μl := stratumMeasure C sf U d μ
  let : IsFiniteMeasure μl := stratumMeasure_finite C sf U hU d μ
  have hml := stratumMeasure_represents C sf U hU hz d μ hm
  have heq : leadingMeasure (chain C U hU) (strongFeller C sf U hU)
      (stratumData C sf U hU hz d) = μl := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    change (∫ x, f x ∂(stratumData C sf U hU hz d).eigenmeasure
      (LayerRankOne.actual_transfer_positive (chain C U hU) (strongFeller C sf U hU))) = _
    rw [← (stratumData C sf U hU hz d).eigenmeasure_represents
      (LayerRankOne.actual_transfer_positive (chain C U hU) (strongFeller C sf U hU))]
    exact hml f
  change (eigenvectorMeasure _ _).map Subtype.val = _
  rw [heq]
  exact map_stratum_product_eq_closed_product C sf U hU hz d μ hm
end Conull

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (P A : Set X) (hP : IsCompact P) (hA : IsOpen A)
  (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)
  (zeroA : ∀ x, C.killedTransition x A = 0)

local notation "hU" => hP.measurableSet.diff hA.measurableSet
set_option quotPrecheck false in
local notation "hInner" => (hP.measurableSet.diff hA.measurableSet).preimage measurable_subtype_coe
local notation "CP" => chain C P hP.measurableSet
local notation "sP" => strongFeller C sf P hP.measurableSet
local notation "CI" => chain CP (innerLevel (P \ A) P) hInner
local notation "sI" => strongFeller CP sP (innerLevel (P \ A) P) hInner
local notation "CD" => chain C (P \ A) hU
local notation "sD" => strongFeller C sf (P \ A) hU

include hA zeroA in
/-- Removing A is conull for the actual prefix transition, because the
original killed transition never reaches A. -/
theorem zero_inner_complement :
    ∀ x : P, (CP).killedTransition x (innerLevel (P \ A) P)ᶜ = 0 := by
  intro x
  rw [RestrictedLayerChain.killedTransition]
  change (SubtypeKernel.restrict C.killedTransition P hP.measurableSet x)
    ((Subtype.val : P → X) ⁻¹' (P \ A))ᶜ = 0
  rw [SubtypeKernel.restrict_apply_set _ P hP.measurableSet x _
    ((hP.measurableSet.diff hA.measurableSet).preimage measurable_subtype_coe).compl]
  apply measure_mono_null _ (zeroA x.val)
  rintro y ⟨z, hz, rfl⟩
  change ¬(z.val ∈ P \ A) at hz
  by_contra hn
  exact hz ⟨z.property, hn⟩

include zeroA in
/-- The literal live-prefix gap and its ambient probability are constructed
from the one produced compact-prefix rank-one datum. -/
theorem exists_normalizedGap
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CP sP) (1 : P →ᵇ ℝ))
    (Λ : Set X) (positive : ∀ x : P, x.val ∈ Λ → 0 < d.eigenvector x) :
    letI : CompactSpace P := isCompact_iff_compactSpace.mp hP
    letI : CompactSpace ↥(P \ A) := isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
    letI : CompactSpace (innerLevel (P \ A) P) := isCompact_iff_compactSpace.mp
      ((hP.isClosed.inter hA.isClosed_compl).preimage continuous_subtype_val).isCompact
    ∃ ν : ProbabilityMeasure ↥(P \ A),
      Paper.LocalConclusions.NormalizedGap CD {x : ↥(P \ A) | x.val ∈ Λ} ν ∧
      (ν : Measure ↥(P \ A)).map Subtype.val =
        (productMeasure CP sP d).map Subtype.val := by
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let : CompactSpace ↥(P \ A) := isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
  let : CompactSpace (innerLevel (P \ A) P) := isCompact_iff_compactSpace.mp
    ((hP.isClosed.inter hA.isClosed_compl).preimage continuous_subtype_val).isCompact
  let hz := zero_inner_complement P A hP hA C zeroA
  let di := stratumData CP sP (innerLevel (P \ A) P) hInner hz d
  let dd := NestedNormalizedGap.data (P \ A) P sdiff_subset C sf hU hP.measurableSet di
  let ν := LayerNormalizedGap.probability CD sD dd
  have hν := NestedNormalizedGap.product_map (P \ A) P sdiff_subset C sf hU hP.measurableSet di
  have hi := conull_product_map CP sP (innerLevel (P \ A) P) hInner hz d
  refine ⟨ν, LayerNormalizedGap.normalizedGap CD sD dd _ ?_, ?_⟩
  · intro x hx
    change 0 < di.eigenvector ((flattenHomeomorph (P \ A) P sdiff_subset).symm x)
    exact stratumData_vector_pos CP sP (innerLevel (P \ A) P) hInner hz d _
      (positive ⟨x.val, x.property.1⟩ hx)
  · change (productMeasure CD sD dd).map Subtype.val = _
    rw [hν, Measure.map_map measurable_subtype_coe
      (flattenHomeomorph (P \ A) P sdiff_subset).measurable, ← hi,
      Measure.map_map measurable_subtype_coe measurable_subtype_coe]
    rfl

end ConditionedStochasticStabilityHyperbolic.Global.LivePrefixNormalizedGap
