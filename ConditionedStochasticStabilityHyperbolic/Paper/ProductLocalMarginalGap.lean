module
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualCompactProductGap

/-! The generated selected product-local gap descends to its exact original
marginal. This is independent of the later prefix/global assembly. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ProductLocalMarginalGap
open LeanShared RegularNoise ActualProductRestrictedChain
variable {X Y ι κ : Type*} [Fintype ι] [Fintype κ]
  [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y]
  (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
  (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
  (hF : Measurable F) (hG : Measurable G)
  (K : Set X) [CompactSpace K] (hK : MeasurableSet K)
  (Q : Set (X × Y)) [CompactSpace Q] (hQ : MeasurableSet Q)
  (productSet : Q = K ×ˢ (univ : Set Y))
  (w : X → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
  (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
local instance compactUniv : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ

include productSet hw0 in
 theorem normalized_gap
    (H : (X × Y) × cube (ι := ι ⊕ κ) ε → X × Y) (hH : Measurable H)
    (maps : H = joint ε F G)
    (νP : ProbabilityMeasure Q) (ν : ProbabilityMeasure K)
    (marginal : (ν : Measure K).map Subtype.val = (νP : Measure Q).map (fun z => z.val.1))
    (core : Set X) (y : Y)
    (sf : HasStrongFellerKernel (originalChain L ε F hF K hK w hw R hR bound))
    (νY : ProbabilityMeasure (univ : Set Y))
    (auxiliary : LocalConclusions.NormalizedGap
      (RestrictedNoise.chain (L'.law ε) G hG univ MeasurableSet.univ
        (fun _ => 1) measurable_const 1 zero_lt_one (fun _ => le_rfl)) univ νY)
    (gap : LocalConclusions.NormalizedGap
      (RestrictedNoise.chain ((productLaws L L').law ε) H hH Q hQ
        (fun z => w z.val.1) ((hw.comp measurable_fst).comp measurable_subtype_coe)
        R hR (fun z => bound z.val.1)) {z : Q | z.val ∈ core ×ˢ (univ : Set Y)} νP) :
    LocalConclusions.NormalizedGap (originalChain L ε F hF K hK w hw R hR bound)
      {x : K | x.val ∈ core} ν := by
  subst Q
  subst H
  let : CompactSpace (K ×ˢ (univ : Set Y)) := (LiveProductCoordinates.liveProduct K).symm.compactSpace
  have chainEq : productChain L L' ε F G hF hG K hK w hw R 1 hR le_rfl bound =
      RestrictedNoise.chain ((productLaws L L').law ε) (joint ε F G) hH
        (K ×ˢ (univ : Set Y)) hQ (fun z => w z.val.1)
        ((hw.comp measurable_fst).comp measurable_subtype_coe) R hR (fun z => bound z.val.1) := by
    unfold productChain
    simp only [mul_one]
  rw [← chainEq] at gap
  have productGap : LocalConclusions.NormalizedGap
      (productChain L L' ε F G hF hG K hK w hw R 1 hR le_rfl bound)
      {z | (LiveProductCoordinates.liveProduct K z).1.val ∈ core ∧
        (LiveProductCoordinates.liveProduct K z).2 = y} νP := by
    obtain ⟨sfP, dP, product, positive⟩ := gap
    refine ⟨sfP, dP, product, ?_⟩
    intro z hz
    exact positive z ⟨hz.1, mem_univ _⟩
  have produced := ActualCompactProductGap.normalizedGap L L' ε F G hF hG K hK
    w hw hw0 R 1 hR le_rfl bound sf νY auxiliary νP {x : K | x.val ∈ core} y productGap
  have same : ν = νP.map (fun z => (LiveProductCoordinates.liveProduct K z).1) := by
    apply ProbabilityMeasure.toMeasure_injective
    apply (MeasurableEmbedding.subtype_coe hK).map_injective
    change (ν : Measure K).map Subtype.val =
      ((νP : Measure (K ×ˢ (univ : Set Y))).map
        (fun z => (LiveProductCoordinates.liveProduct K z).1)).map Subtype.val
    have measurableProjection : Measurable (fun z : K ×ˢ (univ : Set Y) =>
        (LiveProductCoordinates.liveProduct K z).1) :=
      (continuous_fst.comp (LiveProductCoordinates.liveProduct K).continuous).measurable
    rw [Measure.map_map measurable_subtype_coe measurableProjection]
    exact marginal
  exact same ▸ produced
end ConditionedStochasticStabilityHyperbolic.Paper.ProductLocalMarginalGap
