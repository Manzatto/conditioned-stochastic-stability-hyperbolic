module

public import ConditionedStochasticStabilityHyperbolic.Paper.ActualClosedProductChain
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapFamilyWindow
public import ConditionedStochasticStabilityHyperbolic.Paper.ReindexedProductLocalFamily
public import ConditionedStochasticStabilityHyperbolic.Spectral.FullLiveNoiseGap

/-! Apply the stabilizing-product descent to the actual independent cube
processes. The local theorem and its gap-retention companion supply the same
probability below; neither independence nor an eigenproduct is a cited source. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedLocalPoint
open LeanShared RegularNoise ActualProductRestrictedChain

variable {X Y ι κ : Type*} [Fintype ι] [Fintype κ]
  [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y]
  (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
  (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
  (hF : Measurable F) (hG : Measurable G)
  (V : Set X) (w : X → ℝ) (hw : Measurable w)
  (hw0 : ∀ x, 0 ≤ w x) (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY)
  (bound : ∀ x, w x ≤ RX)

local instance stabilizedProbability (J : Laws (ι := κ)) (δ : ℝ≥0) :
    IsProbabilityMeasure (J.law δ) := J.probability δ

local instance stabilizedCompactUniv : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ
local instance stabilizedCompactCollar : CompactSpace (closure V) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact
local instance stabilizedCompactProductCollar : CompactSpace (closure (Set.prod V (univ : Set Y))) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

local notation "C" => originalChain L ε F hF (closure V)
  isClosed_closure.measurableSet w hw RX hRX bound
local notation "D₀" => RestrictedNoise.chain (L'.law ε) G hG univ
  MeasurableSet.univ (fun _ => 1) measurable_const RY
  (lt_of_lt_of_le zero_lt_one hRY) (fun _ => hRY)
@[expose] def closedChain := RestrictedNoise.chain (Laws.law (productLaws L L') ε) (joint ε F G)
  (measurable_joint ε F G hF hG) (closure (Set.prod V (univ : Set Y)))
  isClosed_closure.measurableSet (fun z => w (Prod.fst (Subtype.val z)))
  ((hw.comp measurable_fst).comp measurable_subtype_coe) (RX * RY)
  (mul_pos hRX (lt_of_lt_of_le zero_lt_one hRY))
  (fun z => (bound z.val.1).trans (le_mul_of_one_le_right hRX.le hRY))

local notation "CD" => closedChain L L' ε F G hF hG V w hw RX RY hRX hRY bound


include hw0 in
/-- The prescribed marginal has every local conclusion for the actual
original process, with its original normalization RX. The auxiliary theorem
uses the literal whole-live subtype, which is transported internally. -/
theorem point
    (Λ : Set X) (hΛ : (closure V ∩ Λ).Nonempty)
    (sf : HasStrongFellerKernel C)
    (νY : ProbabilityMeasure (univ : Set Y))
    (auxiliary : LocalConclusions.NormalizedGap D₀ univ νY)
    (ν : ProbabilityMeasure (closure (Set.prod V (univ : Set Y))))
    (localPoint : LocalConclusions.Point CD (RX * RY)
      {z | Prod.fst (Subtype.val z) ∈ Λ} ν)
    (localGap : LocalConclusions.NormalizedGap CD {z | Prod.fst (Subtype.val z) ∈ Λ} ν)
    (y : Y) :
    LocalConclusions.Point C RX {x | x.val ∈ Λ}
      (ν.map (fun z => ((LiveProductCoordinates.closedCollar V) z).1)) := by
  obtain ⟨sy, dy, _, _⟩ := auxiliary
  obtain ⟨dy', _⟩ := FullLiveNoiseGap.spectralData (L'.law ε) G hG RY
    (lt_of_lt_of_le zero_lt_one hRY) hRY sy dy
  obtain ⟨sxy, dxy, hproduct, hpositive⟩ := localGap
  let e : ((closure V) × Y) ≃ₜ closure (Set.prod V (univ : Set Y)) :=
    (LiveProductCoordinates.closedCollar V).symm
  have hcore : ({x : closure V | x.val ∈ Λ} : Set (closure V)).Nonempty := by
    obtain ⟨x, hx, hxl⟩ := hΛ
    exact ⟨⟨x, hx⟩, hxl⟩
  have hsupport : ∀ x ∈ ({x : closure V | x.val ∈ Λ} : Set (closure V)),
      e (x, y) ∈ (ν : Measure (closure (Set.prod V (univ : Set Y)))).support := by
    intro x hx
    apply localPoint.2.1
    exact hx
  have hp : ∀ x ∈ ({x : closure V | x.val ∈ Λ} : Set (closure V)),
      0 < dxy.eigenvector (e (x, y)) := by
    intro x hx
    exact hpositive (e (x, y)) hx
  exact ReindexedProductLocalFamily.point_marginal C
    (auxiliaryChain L' ε G hG RY hRY) CD sf
    (FullLiveNoiseGap.strongFeller (L'.law ε) G hG RY
      (lt_of_lt_of_le zero_lt_one hRY) hRY sy) sxy e
    (closed_independent L L' ε F G hF hG V w hw hw0 RX RY hRX hRY bound)
    dy' RY⁻¹ (FullNoiseSurvival.transfer_one (L'.law ε) G hG RY
      (lt_of_lt_of_le zero_lt_one hRY) hRY _) dxy ν hproduct
    {x | x.val ∈ Λ} hcore y hsupport hp RX hRX

end ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedLocalPoint
