module

public import ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedLocalPoint
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualProductNoiseChain

/-! The endpoint descent on the literal regular-noise families. Joint C¹
supplies map measurability; the input gaps and product Point are the outputs
of the actual local theorem and gap-retention companion, for the same ν. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedNoisePoint
open LeanShared RegularNoise ActualProductRestrictedChain
variable {X Y E H ι κ : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y] [ChartedSpace E X] [ChartedSpace H Y]
  {T : X ≃ₜ X} {T' : Y ≃ₜ Y} {r : ℝ}
  (P : Maps (E := E) (ι := ι) T r) (Q : Maps (E := H) (ι := κ) T' r)
  (L : Laws (ι := ι)) (L' : Laws (ι := κ))
  (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ min P.window Q.window)
  (V : Set X) (w : X → ℝ) (hw : Measurable w)
  (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY) (bound : ∀ x, w x ≤ RX)

local instance stabilizedNoiseCompactUniv : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ
local instance stabilizedNoiseCompactCollar : CompactSpace (closure V) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact
local instance stabilizedNoiseCompactProduct : CompactSpace (closure (Set.prod V (univ : Set Y))) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

@[expose] def original := originalChain L ε (actualMap P ε)
  (actualMap_measurable P ε hε (le_min_iff.mp hwindow).1)
  (closure V) isClosed_closure.measurableSet w hw RX hRX bound

@[expose] def auxiliaryLocal := RestrictedNoise.chain (L'.law ε) (actualMap Q ε)
  (actualMap_measurable Q ε hε (le_min_iff.mp hwindow).2)
  univ MeasurableSet.univ (fun _ => 1) measurable_const RY
  (lt_of_lt_of_le zero_lt_one hRY) (fun _ => hRY)

@[expose] def closedProduct := ActualStabilizedLocalPoint.closedChain L L' ε
  (actualMap P ε) (actualMap Q ε)
  (actualMap_measurable P ε hε (le_min_iff.mp hwindow).1)
  (actualMap_measurable Q ε hε (le_min_iff.mp hwindow).2)
  V w hw RX RY hRX hRY bound

/-- The actual two families construct the original local conclusion with
normalizer RX from the product conclusion with normalizer RX*RY. -/
theorem point
    (nonnegative : ∀ x, 0 ≤ w x) (Λ : Set X) (hΛ : (closure V ∩ Λ).Nonempty)
    (sf : HasStrongFellerKernel (original P Q L ε hε hwindow V w hw RX hRX bound))
    (νY : ProbabilityMeasure (univ : Set Y))
    (auxiliary : LocalConclusions.NormalizedGap
      (auxiliaryLocal P Q L' ε hε hwindow RY hRY) univ νY)
    (ν : ProbabilityMeasure (closure (Set.prod V (univ : Set Y))))
    (localPoint : LocalConclusions.Point
      (closedProduct P Q L L' ε hε hwindow V w hw RX RY hRX hRY bound)
      (RX * RY) {z | z.val.1 ∈ Λ} ν)
    (localGap : LocalConclusions.NormalizedGap
      (closedProduct P Q L L' ε hε hwindow V w hw RX RY hRX hRY bound)
      {z | z.val.1 ∈ Λ} ν) (y : Y) :
    LocalConclusions.Point (original P Q L ε hε hwindow V w hw RX hRX bound)
      RX {x | x.val ∈ Λ}
      (ν.map (fun z => ((LiveProductCoordinates.closedCollar V) z).1)) := by
  exact ActualStabilizedLocalPoint.point L L' ε (actualMap P ε) (actualMap Q ε)
    (actualMap_measurable P ε hε (le_min_iff.mp hwindow).1)
    (actualMap_measurable Q ε hε (le_min_iff.mp hwindow).2)
    V w hw nonnegative RX RY hRX hRY bound Λ hΛ sf νY auxiliary ν localPoint localGap y

end ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedNoisePoint
