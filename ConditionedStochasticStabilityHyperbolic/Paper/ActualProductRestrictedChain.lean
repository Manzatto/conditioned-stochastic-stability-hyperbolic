module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductRegularNoiseKernels
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise
public import LeanShared.Probability.DepartureWeightedRandomMap
public import LeanShared.Probability.LiveProductKernel

/-! The original cube laws construct the independence used in stabilizing
spectral descent. The product normalizer is exactly RX*RY. The auxiliary
state is the whole Y, while the first factor retains its literal live subtype. -/

public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualProductRestrictedChain
open LeanShared RegularNoise
variable {X Y ι κ : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace X] [MeasurableSpace Y]

local instance actualProductRestrictedChainProbability (L : Laws (ι := ι)) (ε : ℝ≥0) :
    IsProbabilityMeasure (L.law ε) := L.probability ε

@[expose] def joint (ε : ℝ≥0)
    (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y) :
    (X × Y) × cube (ι := ι ⊕ κ) ε → X × Y := fun z =>
  (F (z.1.1, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).1),
    G (z.1.2, (NoiseCubeRescaling.splitCube (ε : ℝ) z.2).2))

 theorem measurable_joint (ε : ℝ≥0)
    (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
    (hF : Measurable F) (hG : Measurable G) : Measurable (joint ε F G) :=
  (hF.comp (measurable_fst.fst.prodMk
    ((NoiseCubeRescaling.splitCube (ε : ℝ)).measurable.comp measurable_snd).fst)).prodMk
      (hG.comp (measurable_fst.snd.prodMk
        ((NoiseCubeRescaling.splitCube (ε : ℝ)).measurable.comp measurable_snd).snd))

/-- Exact ambient factorization, including original departure weights and
both live indicators. It uses the constructed sum-cube product law. -/
theorem ambient_independent
    (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
    (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
    (hF : Measurable F) (hG : Measurable G)
    (K : Set X) (hK : MeasurableSet K) (w : X → ℝ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY)
    (bound : ∀ x, w x ≤ RX) (x : X) (y : Y) :
    (NoiseKernel.chain ((productLaws L L').law ε) (joint ε F G)
      (measurable_joint ε F G hF hG) (K ×ˢ univ) (hK.prod MeasurableSet.univ)
      (fun z => w z.1) (hw.comp measurable_fst) (RX * RY)
      (mul_pos hRX (lt_of_lt_of_le zero_lt_one hRY))
      (fun z => (bound z.1).trans (le_mul_of_one_le_right hRX.le hRY))).killedTransition (x, y) =
    ((NoiseKernel.chain (L.law ε) F hF K hK w hw RX hRX bound).killedTransition x).prod
      ((NoiseKernel.chain (L'.law ε) G hG univ MeasurableSet.univ (fun _ => 1)
        measurable_const RY (lt_of_lt_of_le zero_lt_one hRY) (fun _ => hRY)).killedTransition y) := by
  simp only [NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  rw [← DepartureWeightedRandomMap.normalized_killed _ _ _ _ _ (measurable_joint ε F G hF hG),
    ← DepartureWeightedRandomMap.normalized_killed _ _ _ _ _ hF,
    ← DepartureWeightedRandomMap.normalized_killed _ _ _ _ _ hG]
  have weight : (fun z : (X × Y) × cube (ι := ι ⊕ κ) ε => w z.1.1 / (RX * RY)) =
      (fun z => (w z.1.1 / RX) * (1 / RY)) := by
    funext z
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [weight]
  exact productLaws_killed L L' ε (fun z => w z.1 / RX) (fun _ => 1 / RY)
    ((hw.comp measurable_fst).div_const RX) measurable_const
    (fun x _ => div_nonneg (hw0 x) hRX.le) F G hF hG K univ hK MeasurableSet.univ x y

section Live
variable [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y]

/-- The literal original live-state chain. -/
@[expose] def originalChain
    (L : Laws (ι := ι)) (ε : ℝ≥0) (F : X × cube (ι := ι) ε → X) (hF : Measurable F)
    (K : Set X) (hK : MeasurableSet K) (w : X → ℝ) (hw : Measurable w)
    (RX : ℝ) (hRX : 0 < RX) (bound : ∀ x, w x ≤ RX) :=
  RestrictedNoise.chain (L.law ε) F hF K hK (fun x => w x.val)
    (hw.comp measurable_subtype_coe) RX hRX (fun x => bound x.val)

/-- The auxiliary factor has no live-state subtype and constant weight one. -/
@[expose] def auxiliaryChain
    (L' : Laws (ι := κ)) (ε : ℝ≥0) (G : Y × cube (ι := κ) ε → Y) (hG : Measurable G)
    (RY : ℝ) (hRY : 1 ≤ RY) :=
  NoiseKernel.chain (L'.law ε) G hG univ MeasurableSet.univ (fun _ => 1)
    measurable_const RY (lt_of_lt_of_le zero_lt_one hRY) (fun _ => hRY)

/-- The actual independent sum-cube chain, with the product normalizer. -/
@[expose] def productChain
    (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
    (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
    (hF : Measurable F) (hG : Measurable G)
    (K : Set X) (hK : MeasurableSet K) (w : X → ℝ) (hw : Measurable w)
    (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY) (bound : ∀ x, w x ≤ RX) :=
  RestrictedNoise.chain ((productLaws L L').law ε) (joint ε F G)
    (measurable_joint ε F G hF hG) (K ×ˢ univ) (hK.prod MeasurableSet.univ)
    (fun z => w z.val.1) ((hw.comp measurable_fst).comp measurable_subtype_coe)
    (RX * RY) (mul_pos hRX (lt_of_lt_of_le zero_lt_one hRY))
    (fun z => (bound z.val.1).trans (le_mul_of_one_le_right hRX.le hRY))

/-- The exact independence premise of ReindexedProductLocalFamily,
constructed from the actual laws and maps rather than supplied as a source. -/
theorem restricted_independent
    (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
    (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
    (hF : Measurable F) (hG : Measurable G)
    (K : Set X) (hK : MeasurableSet K) (w : X → ℝ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY)
    (bound : ∀ x, w x ≤ RX) (x : K) (y : Y) :
    ((productChain L L' ε F G hF hG K hK w hw RX RY hRX hRY bound).killedTransition
      ((LiveProductCoordinates.liveProduct K).symm (x, y))).map
        (LiveProductCoordinates.liveProduct K) =
      ((originalChain L ε F hF K hK w hw RX hRX bound).killedTransition x).prod
        ((auxiliaryChain L' ε G hG RY hRY).killedTransition y) := by
  let A := NoiseKernel.chain (L.law ε) F hF K hK w hw RX hRX bound
  let B := auxiliaryChain L' ε G hG RY hRY
  let P := NoiseKernel.chain ((productLaws L L').law ε) (joint ε F G)
    (measurable_joint ε F G hF hG) (K ×ˢ univ) (hK.prod MeasurableSet.univ)
    (fun z => w z.1) (hw.comp measurable_fst) (RX * RY)
    (mul_pos hRX (lt_of_lt_of_le zero_lt_one hRY))
    (fun z => (bound z.1).trans (le_mul_of_one_le_right hRX.le hRY))
  let : IsFiniteKernel A.killedTransition := ⟨1, ENNReal.one_lt_top, A.killedTransition_mass_le_one⟩
  let : IsFiniteKernel B.killedTransition := ⟨1, ENNReal.one_lt_top, B.killedTransition_mass_le_one⟩
  have independent : ∀ a b, P.killedTransition (a, b) =
      (A.killedTransition a).prod (B.killedTransition b) :=
    ambient_independent L L' ε F G hF hG K hK w hw hw0 RX RY hRX hRY bound
  have first : (originalChain L ε F hF K hK w hw RX hRX bound).killedTransition =
      SubtypeKernel.restrict A.killedTransition K hK :=
    RestrictedNoise.killedTransition_eq_restrict (L.law ε) F hF K hK
      (fun z => w z.val) (hw.comp measurable_subtype_coe) RX hRX (fun z => bound z.val)
      w hw bound (fun _ => rfl)
  have prod : (productChain L L' ε F G hF hG K hK w hw RX RY hRX hRY bound).killedTransition =
      SubtypeKernel.restrict P.killedTransition (K ×ˢ univ) (hK.prod MeasurableSet.univ) :=
    RestrictedNoise.killedTransition_eq_restrict ((productLaws L L').law ε)
      (joint ε F G) (measurable_joint ε F G hF hG) (K ×ˢ univ) (hK.prod MeasurableSet.univ)
      (fun z => w z.val.1) ((hw.comp measurable_fst).comp measurable_subtype_coe)
      (RX * RY) (mul_pos hRX (lt_of_lt_of_le zero_lt_one hRY))
      (fun z => (bound z.val.1).trans (le_mul_of_one_le_right hRX.le hRY))
      (fun z => w z.1) (hw.comp measurable_fst)
      (fun z => (bound z.1).trans (le_mul_of_one_le_right hRX.le hRY)) (fun _ => rfl)
  rw [prod, first]
  exact LiveProductCoordinates.map_restricted_kernel_product A.killedTransition
    B.killedTransition P.killedTransition independent K hK
    ((LiveProductCoordinates.liveProduct K).symm (x, y))

end Live
end ConditionedStochasticStabilityHyperbolic.Paper.ActualProductRestrictedChain
