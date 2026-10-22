module

public import ConditionedStochasticStabilityHyperbolic.Paper.ActualCompactProductGap
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualProductNoiseChain

/-! Arbitrary compact live-set endpoint descent for the actual regular-noise
families, retaining the exact product probability's first marginal and any
pointwise positivity region. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualCompactNoiseGap
open LeanShared RegularNoise ActualProductRestrictedChain
variable {X Y E H ι κ : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y] [ChartedSpace E X] [ChartedSpace H Y]
  {T : X ≃ₜ X} {T' : Y ≃ₜ Y} {r : ℝ}
  (P : Maps (E := E) (ι := ι) T r) (Q : Maps (E := H) (ι := κ) T' r)
  (L : Laws (ι := ι)) (L' : Laws (ι := κ))
  (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ min P.window Q.window)
  (K : Set X) [CompactSpace K] (hK : MeasurableSet K)
  (w : X → ℝ) (hw : Measurable w)
  (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY) (bound : ∀ x, w x ≤ RX)

local instance compactNoiseGapUniv : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ
local instance compactNoiseGapProduct : CompactSpace (K ×ˢ (univ : Set Y)) :=
  (LiveProductCoordinates.liveProduct K).symm.compactSpace

@[expose] def original := originalChain L ε (actualMap P ε)
  (actualMap_measurable P ε hε (le_min_iff.mp hwindow).1)
  K hK w hw RX hRX bound

@[expose] def auxiliaryLocal := RestrictedNoise.chain (L'.law ε) (actualMap Q ε)
  (actualMap_measurable Q ε hε (le_min_iff.mp hwindow).2)
  univ MeasurableSet.univ (fun _ => 1) measurable_const RY
  (lt_of_lt_of_le zero_lt_one hRY) (fun _ => hRY)

@[expose] def compactProduct := productChain L L' ε
  (actualMap P ε) (actualMap Q ε)
  (actualMap_measurable P ε hε (le_min_iff.mp hwindow).1)
  (actualMap_measurable Q ε hε (le_min_iff.mp hwindow).2)
  K hK w hw RX RY hRX hRY bound

/-- This applies to K=Aᶜ as well as to collar closures. The original gap
and same marginal eigenproduct are derived without mixing assumptions. -/
theorem normalizedGap
    (nonnegative : ∀ x, 0 ≤ w x)
    (sf : HasStrongFellerKernel (original P Q L ε hε hwindow K hK w hw RX hRX bound))
    (νY : ProbabilityMeasure (univ : Set Y))
    (auxiliary : LocalConclusions.NormalizedGap
      (auxiliaryLocal P Q L' ε hε hwindow RY hRY) univ νY)
    (ν : ProbabilityMeasure (K ×ˢ (univ : Set Y)))
    (region : Set K) (y : Y)
    (productGap : LocalConclusions.NormalizedGap
      (compactProduct P Q L L' ε hε hwindow K hK w hw RX RY hRX hRY bound)
      {z | (LiveProductCoordinates.liveProduct K z).1 ∈ region ∧
        (LiveProductCoordinates.liveProduct K z).2 = y} ν) :
    LocalConclusions.NormalizedGap
      (original P Q L ε hε hwindow K hK w hw RX hRX bound) region
      (ν.map (fun z => (LiveProductCoordinates.liveProduct K z).1)) := by
  exact ActualCompactProductGap.normalizedGap L L' ε (actualMap P ε) (actualMap Q ε)
    (actualMap_measurable P ε hε (le_min_iff.mp hwindow).1)
    (actualMap_measurable Q ε hε (le_min_iff.mp hwindow).2)
    K hK w hw nonnegative RX RY hRX hRY bound sf νY auxiliary ν region y productGap

end ConditionedStochasticStabilityHyperbolic.Paper.ActualCompactNoiseGap
