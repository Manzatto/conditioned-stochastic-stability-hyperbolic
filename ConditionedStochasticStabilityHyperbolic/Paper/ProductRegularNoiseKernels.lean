module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductRegularNoiseLaws
public import LeanShared.Probability.WeightedRandomMapReparametrization
public import LeanShared.Probability.IndependentWeightedRandomMaps

/-! The literal sum-cube independent law gives the product of the actual
weighted transitions and killed transitions. Thus stabilization changes
neither factor law nor either live indicator. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared WeightedRandomMapKernel

variable {ι κ X X' Y Y' : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y] [MeasurableSpace Y']

local instance laws_probability (L : Laws (ι := ι)) (ε : ℝ≥0) :
    IsProbabilityMeasure (L.law ε) := L.probability ε

/-- Exact weighted kernel factorization on the manuscript's single cube. -/
theorem productLaws_transition
    (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
    (W : X × cube (ι := ι) ε → ℝ) (W' : X' × cube (ι := κ) ε → ℝ)
    (hW : Measurable W) (hW' : Measurable W') (hW0 : ∀ x v, 0 ≤ W (x, v))
    (F : X × cube (ι := ι) ε → Y) (F' : X' × cube (ι := κ) ε → Y')
    (hF : Measurable F) (hF' : Measurable F') (x : X) (x' : X') :
    transition ((productLaws L L').law ε)
      (fun z : (X × X') × cube (ι := ι ⊕ κ) ε =>
        W (z.1.1, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).1) *
        W' (z.1.2, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).2))
      (fun z : (X × X') × cube (ι := ι ⊕ κ) ε =>
        (F (z.1.1, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).1),
          F' (z.1.2, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).2))) (x, x') =
      (transition (L.law ε) W F x).prod (transition (L'.law ε) W' F' x') := by
  change transition (((L.law ε).prod (L'.law ε)).map
    (NoiseCubeRescaling.splitCube (ε : ℝ)).symm)
    (fun z => independentWeight W W' (z.1, NoiseCubeRescaling.splitCube (ε : ℝ) z.2))
    (fun z => independentMap F F' (z.1, NoiseCubeRescaling.splitCube (ε : ℝ) z.2)) (x, x') = _
  rw [transition_reparametrization (NoiseCubeRescaling.splitCube (ε : ℝ))
    ((L.law ε).prod (L'.law ε)) (independentWeight W W') (independentWeight_measurable hW hW')
    (independentMap F F') (independentMap_measurable hF hF')]
  exact independent_transition (L.law ε) (L'.law ε) W W' hW hW' hW0 F F' hF hF' x x'

/-- Exact killed kernel factorization, including the product live set. -/
theorem productLaws_killed
    (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
    (W : X × cube (ι := ι) ε → ℝ) (W' : X' × cube (ι := κ) ε → ℝ)
    (hW : Measurable W) (hW' : Measurable W') (hW0 : ∀ x v, 0 ≤ W (x, v))
    (F : X × cube (ι := ι) ε → Y) (F' : X' × cube (ι := κ) ε → Y')
    (hF : Measurable F) (hF' : Measurable F')
    (K : Set Y) (K' : Set Y') (hK : MeasurableSet K) (hK' : MeasurableSet K')
    (x : X) (x' : X') :
    killed ((productLaws L L').law ε)
      (fun z : (X × X') × cube (ι := ι ⊕ κ) ε =>
        W (z.1.1, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).1) *
        W' (z.1.2, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).2))
      (fun z : (X × X') × cube (ι := ι ⊕ κ) ε =>
        (F (z.1.1, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).1),
          F' (z.1.2, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).2)))
      (K ×ˢ K') (hK.prod hK') (x, x') =
      (killed (L.law ε) W F K hK x).prod (killed (L'.law ε) W' F' K' hK' x') := by
  change killed (((L.law ε).prod (L'.law ε)).map
    (NoiseCubeRescaling.splitCube (ε : ℝ)).symm)
    (fun z => independentWeight W W' (z.1, NoiseCubeRescaling.splitCube (ε : ℝ) z.2))
    (fun z => independentMap F F' (z.1, NoiseCubeRescaling.splitCube (ε : ℝ) z.2))
    (K ×ˢ K') (hK.prod hK') (x, x') = _
  rw [killed_reparametrization (NoiseCubeRescaling.splitCube (ε : ℝ))
    ((L.law ε).prod (L'.law ε)) (independentWeight W W') (independentWeight_measurable hW hW')
    (independentMap F F') (independentMap_measurable hF hF') (K ×ˢ K') (hK.prod hK')]
  exact independent_killed (L.law ε) (L'.law ε) W W' hW hW' hW0 F F' hF hF' K K' hK hK' x x'

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
