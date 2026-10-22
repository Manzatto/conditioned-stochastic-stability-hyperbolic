module

public import ConditionedStochasticStabilityHyperbolic.Paper.ActualProductRestrictedChain

/-! Exact independent-kernel descent on the literal closure of the product
collar, using its actual closedCollar homeomorphism. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualProductRestrictedChain
open LeanShared RegularNoise
variable {X Y ι κ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y]
local instance actualClosedProductChainProbability (L : Laws (ι := ι)) (ε : ℝ≥0) :
    IsProbabilityMeasure (L.law ε) := L.probability ε

private theorem independent_of_live_eq
    (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
    (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
    (hF : Measurable F) (hG : Measurable G)
    (K : Set X) (hK : MeasurableSet K) (S : Set (X × Y)) (hS : MeasurableSet S)
    (equal : S = K ×ˢ (univ : Set Y)) (w : X → ℝ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY)
    (bound : ∀ x, w x ≤ RX) (x : K) (y : Y) :
    ((RestrictedNoise.chain ((productLaws L L').law ε) (joint ε F G)
      (measurable_joint ε F G hF hG) S hS (fun z => w z.val.1)
      ((hw.comp measurable_fst).comp measurable_subtype_coe) (RX * RY)
      (mul_pos hRX (lt_of_lt_of_le zero_lt_one hRY))
      (fun z => (bound z.val.1).trans (le_mul_of_one_le_right hRX.le hRY))).killedTransition
      ((((Homeomorph.setCongr equal).trans (LiveProductCoordinates.liveProduct K))).symm (x, y))).map
        ((Homeomorph.setCongr equal).trans (LiveProductCoordinates.liveProduct K)) =
      ((originalChain L ε F hF K hK w hw RX hRX bound).killedTransition x).prod
        ((auxiliaryChain L' ε G hG RY hRY).killedTransition y) := by
  subst S
  change ((productChain L L' ε F G hF hG K hK w hw RX RY hRX hRY bound).killedTransition
      ((LiveProductCoordinates.liveProduct K).symm (x, y))).map
        (LiveProductCoordinates.liveProduct K) = _
  exact restricted_independent L L' ε F G hF hG K hK w hw hw0 RX RY hRX hRY bound x y

theorem closed_independent
    (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
    (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
    (hF : Measurable F) (hG : Measurable G)
    (V : Set X) (w : X → ℝ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY)
    (bound : ∀ x, w x ≤ RX) (x : closure V) (y : Y) :
    ((RestrictedNoise.chain ((productLaws L L').law ε) (joint ε F G)
      (measurable_joint ε F G hF hG) (closure (V ×ˢ (univ : Set Y))) isClosed_closure.measurableSet (fun z => w z.val.1)
      ((hw.comp measurable_fst).comp measurable_subtype_coe) (RX * RY)
      (mul_pos hRX (lt_of_lt_of_le zero_lt_one hRY))
      (fun z => (bound z.val.1).trans (le_mul_of_one_le_right hRX.le hRY))).killedTransition
      ((LiveProductCoordinates.closedCollar V).symm (x, y))).map
        (LiveProductCoordinates.closedCollar V) =
      ((originalChain L ε F hF (closure V) isClosed_closure.measurableSet w hw RX hRX bound).killedTransition x).prod
        ((auxiliaryChain L' ε G hG RY hRY).killedTransition y) := by
  exact independent_of_live_eq L L' ε F G hF hG (closure V) isClosed_closure.measurableSet
    (closure (V ×ˢ (univ : Set Y))) isClosed_closure.measurableSet
    (by rw [closure_prod_eq, closure_univ]) w hw hw0 RX RY hRX hRY bound x y

end ConditionedStochasticStabilityHyperbolic.Paper.ActualProductRestrictedChain
