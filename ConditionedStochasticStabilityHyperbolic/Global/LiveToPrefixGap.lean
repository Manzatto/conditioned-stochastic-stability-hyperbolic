module

public import ConditionedStochasticStabilityHyperbolic.Global.ConullGapExtension
public import ConditionedStochasticStabilityHyperbolic.Global.NestedGapExtension
public import ConditionedStochasticStabilityHyperbolic.Global.LivePrefixNormalizedGap

/-! Extend a derived gap on the literal live prefix back to the compact
prefix used by the all-starting-point global conclusions. The eigenproduct
is preserved exactly under the state inclusion. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.LiveToPrefixGap
open LeanShared ComplexStrongFeller LayerQuasiErgodic NestedLayerKernel
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (P A : Set X) (hP : IsCompact P) (hA : IsOpen A)
  (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)
  (zeroA : ∀ x, C.killedTransition x A = 0)
local notation "hU" => hP.measurableSet.diff hA.measurableSet
set_option quotPrecheck false in
local notation "hInner" => (hP.measurableSet.diff hA.measurableSet).preimage measurable_subtype_coe
local notation "CP" => RestrictedLayerChain.chain C P hP.measurableSet
local notation "sP" => RestrictedLayerChain.strongFeller C sf P hP.measurableSet
local notation "CD" => RestrictedLayerChain.chain C (P \ A) hU
local notation "sD" => RestrictedLayerChain.strongFeller C sf (P \ A) hU

include zeroA in
 theorem exists_prefix_gap (Λ : Set X) (hΛlive : Λ ⊆ Aᶜ) :
    letI : CompactSpace P := isCompact_iff_compactSpace.mp hP
    letI : CompactSpace ↥(P \ A) := isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
    ∀ (ν : ProbabilityMeasure ↥(P \ A)),
    Paper.LocalConclusions.NormalizedGap CD {x : ↥(P \ A) | x.val ∈ Λ} ν →
    ∃ d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CP sP) (1 : P →ᵇ ℝ),
      (∀ x : P, x.val ∈ Λ → 0 < d.eigenvector x) ∧
      (productMeasure CP sP d).map Subtype.val = (ν : Measure ↥(P \ A)).map Subtype.val := by
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let : CompactSpace ↥(P \ A) := isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
  let : CompactSpace (innerLevel (P \ A) P) := isCompact_iff_compactSpace.mp
    ((hP.isClosed.inter hA.isClosed_compl).preimage continuous_subtype_val).isCompact
  intro ν gap
  obtain ⟨sfD, dD, hν, hpositive⟩ := gap
  have hsf : sfD = sD := Subsingleton.elim _ _
  subst sfD
  let dd := dD.rewriteOperator (LayerNormalizedGap.operator_eq CD sD).symm
  have hd : productMeasure CD sD dd = (ν : Measure ↥(P \ A)) := by
    change eigenvectorMeasure (dd.eigenmeasure (LayerRankOne.actual_transfer_positive CD sD)) dd.eigenvector = _
    dsimp only [dd]
    rw [RankOneSpectralData.rewriteOperator_eigenmeasure,
      RankOneSpectralData.rewriteOperator_vector]
    exact hν.symm
  let di := NestedGapExtension.data (P \ A) P sdiff_subset C sf hU hP.measurableSet dd
  let hz := LivePrefixNormalizedGap.zero_inner_complement P A hP hA C zeroA
  let dp := ConullGapExtension.data CP sP (innerLevel (P \ A) P) hInner hz di
  refine ⟨dp, ?_, ?_⟩
  · intro x hx
    let u : ↥(P \ A) := ⟨x.val, x.property, hΛlive hx⟩
    let z : innerLevel (P \ A) P := ⟨x, u.property⟩
    have he := ConullGapExtension.data_vector_on_live CP sP (innerLevel (P \ A) P) hInner hz di z
    change dp.eigenvector x = di.eigenvector z at he
    rw [he]
    change 0 < dd.eigenvector u
    simpa only [dd, RankOneSpectralData.rewriteOperator_vector] using hpositive u hx
  · have hi := ConullGapExtension.productMeasure_eq_map CP sP (innerLevel (P \ A) P) hInner hz di
    have hn := NestedGapExtension.product_map (P \ A) P sdiff_subset C sf hU hP.measurableSet dd
    change (productMeasure CP sP dp).map Subtype.val = _
    rw [hi, ← hd, ← hn,
      Measure.map_map measurable_subtype_coe measurable_subtype_coe,
      Measure.map_map measurable_subtype_coe (flattenHomeomorph (P \ A) P sdiff_subset).measurable]
    rfl
end ConditionedStochasticStabilityHyperbolic.Global.LiveToPrefixGap
