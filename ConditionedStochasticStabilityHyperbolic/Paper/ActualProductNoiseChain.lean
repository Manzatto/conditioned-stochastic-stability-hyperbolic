module

public import ConditionedStochasticStabilityHyperbolic.Paper.ActualClosedProductChain
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductControlGeometry

/-! The literal regular-noise maps supply joint measurability and the exact
independent-family identity. No kernel factorization or measurable-map source
is requested by this final process bridge. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualProductRestrictedChain
open LeanShared RegularNoise
variable {X Y E F ι κ : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopology Y]
  [ChartedSpace E X] [ChartedSpace F Y]
  {T : X ≃ₜ X} {T' : Y ≃ₜ Y} {r : ℝ}

local instance actualProductNoiseChainProbability (L : Laws (ι := ι)) (ε : ℝ≥0) :
    IsProbabilityMeasure (L.law ε) := L.probability ε

@[expose] def actualMap (P : Maps (E := E) (ι := ι) T r) (ε : ℝ≥0) :
    X × cube (ι := ι) ε → X := fun z => P.family ε z.2.val z.1

omit [FiniteDimensional ℝ E] [MeasurableSpace X] [BorelSpace X] in
theorem actualMap_continuous (P : Maps (E := E) (ι := ι) T r)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ P.window) : Continuous (actualMap P ε) := by
  obtain ⟨O, hO, hc, hC⟩ := P.joint_C1 ε hε hw
  exact hC.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
    (fun z => ⟨hc z.2.property, mem_univ z.1⟩)

omit [FiniteDimensional ℝ E] in
theorem actualMap_measurable (P : Maps (E := E) (ι := ι) T r)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ P.window) : Measurable (actualMap P ε) :=
  (actualMap_continuous P ε hε hw).measurable

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y] in
theorem joint_eq_independentFamily (P : Maps (E := E) (ι := ι) T r)
    (Q : Maps (E := F) (ι := κ) T' r) (ε : ℝ≥0) :
    joint ε (actualMap P ε) (actualMap Q ε) =
      (fun z => independentFamily P Q ε z.2.val z.1) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem maps_closed_independent
    (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
    (P : Maps (E := E) (ι := ι) T r) (Q : Maps (E := F) (ι := κ) T' r)
    (hε : 0 < ε) (hwindows : ε ≤ min P.window Q.window)
    (V : Set X) (w : X → ℝ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY)
    (bound : ∀ x, w x ≤ RX) (x : closure V) (y : Y) :
    ((RestrictedNoise.chain ((productLaws L L').law ε) (joint ε (actualMap P ε) (actualMap Q ε))
      (measurable_joint ε (actualMap P ε) (actualMap Q ε)
        (actualMap_measurable P ε hε (le_min_iff.mp hwindows).1)
        (actualMap_measurable Q ε hε (le_min_iff.mp hwindows).2)) (closure (V ×ˢ (univ : Set Y))) isClosed_closure.measurableSet (fun z => w z.val.1)
      ((hw.comp measurable_fst).comp measurable_subtype_coe) (RX * RY)
      (mul_pos hRX (lt_of_lt_of_le zero_lt_one hRY))
      (fun z => (bound z.val.1).trans (le_mul_of_one_le_right hRX.le hRY))).killedTransition
      ((LiveProductCoordinates.closedCollar V).symm (x, y))).map
        (LiveProductCoordinates.closedCollar V) =
      ((originalChain L ε (actualMap P ε) (actualMap_measurable P ε hε (le_min_iff.mp hwindows).1) (closure V) isClosed_closure.measurableSet w hw RX hRX bound).killedTransition x).prod
        ((auxiliaryChain L' ε (actualMap Q ε) (actualMap_measurable Q ε hε (le_min_iff.mp hwindows).2) RY hRY).killedTransition y) := by
  exact closed_independent L L' ε (actualMap P ε) (actualMap Q ε)
    (actualMap_measurable P ε hε (le_min_iff.mp hwindows).1)
    (actualMap_measurable Q ε hε (le_min_iff.mp hwindows).2)
    V w hw hw0 RX RY hRX hRY bound x y

end ConditionedStochasticStabilityHyperbolic.Paper.ActualProductRestrictedChain
