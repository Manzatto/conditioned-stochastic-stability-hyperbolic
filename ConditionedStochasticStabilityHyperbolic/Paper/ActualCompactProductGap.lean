module

public import ConditionedStochasticStabilityHyperbolic.Paper.ActualProductRestrictedChain
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapFamilyWindow
public import ConditionedStochasticStabilityHyperbolic.Spectral.ReindexedSpectralData
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProductGapMarginal
public import ConditionedStochasticStabilityHyperbolic.Spectral.FullLiveNoiseGap

/-! Stabilization descends on an arbitrary compact live set, including the
closed complement of a global absorber. The original normalized gap and its
exact marginal eigenproduct are conclusions, not source assumptions. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualCompactProductGap
open LeanShared RegularNoise ActualProductRestrictedChain ProductSpectralRetraction
variable {X Y ι κ : Type*} [Fintype ι] [Fintype κ]
  [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y]
  (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0)
  (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
  (hF : Measurable F) (hG : Measurable G)
  (K : Set X) [CompactSpace K] (hK : MeasurableSet K)
  (w : X → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
  (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY) (bound : ∀ x, w x ≤ RX)

local instance compactGapUniv : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ
local instance compactGapProduct : CompactSpace (K ×ˢ (univ : Set Y)) :=
  (LiveProductCoordinates.liveProduct K).symm.compactSpace
local instance compactGapProbability (J : Laws (ι := κ)) (δ : ℝ≥0) :
    IsProbabilityMeasure (J.law δ) := J.probability δ

local notation "C" => originalChain L ε F hF K hK w hw RX hRX bound
local notation "D" => auxiliaryChain L' ε G hG RY hRY
local notation "D₀" => RestrictedNoise.chain (L'.law ε) G hG univ
  MeasurableSet.univ (fun _ => 1) measurable_const RY
  (lt_of_lt_of_le zero_lt_one hRY) (fun _ => hRY)
local notation "CD" => productChain L L' ε F G hF hG K hK w hw RX RY hRX hRY bound

include hw0 in
/-- Any pointwise product positivity region descends at the prescribed
auxiliary point. No regular-closed assumption, core support, or mixing is
required. In HG2 the region can be the entire stable basin. -/
theorem normalizedGap
    (sf : HasStrongFellerKernel C)
    (νY : ProbabilityMeasure (univ : Set Y))
    (auxiliary : LocalConclusions.NormalizedGap D₀ univ νY)
    (ν : ProbabilityMeasure (K ×ˢ (univ : Set Y)))
    (region : Set K) (y : Y)
    (productGap : LocalConclusions.NormalizedGap CD
      {z | (LiveProductCoordinates.liveProduct K z).1 ∈ region ∧
        (LiveProductCoordinates.liveProduct K z).2 = y} ν) :
    LocalConclusions.NormalizedGap C region
      (ν.map (fun z => (LiveProductCoordinates.liveProduct K z).1)) := by
  obtain ⟨sy, dy, _, _⟩ := auxiliary
  let sd := FullLiveNoiseGap.strongFeller (L'.law ε) G hG RY
    (lt_of_lt_of_le zero_lt_one hRY) hRY sy
  obtain ⟨dy0, _⟩ := FullLiveNoiseGap.spectralData (L'.law ε) G hG RY
    (lt_of_lt_of_le zero_lt_one hRY) hRY sy dy
  let dy' := dy0.normalizeOne RY⁻¹
    (FullNoiseSurvival.transfer_one (L'.law ε) G hG RY
      (lt_of_lt_of_le zero_lt_one hRY) hRY sd)
  obtain ⟨sxy, dxy, hproduct, hpositive⟩ := productGap
  let e : (K × Y) ≃ₜ (K ×ˢ (univ : Set Y)) :=
    (LiveProductCoordinates.liveProduct K).symm
  let CP := ReindexedCanonicalChain.chain e CD
  let sp := ReindexedCanonicalChain.strongFeller e CD sxy
  let dp := ReindexedCanonicalChain.spectralData e CD sxy dxy
  let PX := strongFellerTransferOperator C sf
  let PY := strongFellerTransferOperator D sd
  let PXY := strongFellerTransferOperator CP sp
  let : IsFiniteKernel (C).killedTransition := by
    change IsFiniteKernel (C).toKilledKernel.kernel
    infer_instance
  let : IsFiniteKernel (D).killedTransition := by
    change IsFiniteKernel (D).toKilledKernel.kernel
    infer_instance
  have repXY (f : K × Y →ᵇ ℝ) (x : K) (z : Y) :
      PXY f (x, z) = ∫ q, f q ∂((C).killedTransition x).prod ((D).killedTransition z) := by
    rw [strongFellerTransferOperator_represents, ReindexedCanonicalChain.killed]
    exact congrArg (fun η : Measure (K × Y) => ∫ q, f q ∂η)
      (restricted_independent L L' ε F G hF hG K hK w hw hw0 RX RY hRX hRY bound x z)
  have oneLift : tensorLift dy'.eigenvector (1 : K →ᵇ ℝ) = (1 : K × Y →ᵇ ℝ) := by
    have hdy : dy'.eigenvector = (1 : Y →ᵇ ℝ) := by
      exact RankOneSpectralData.normalizeOne_eigenvector _ _ _
    rw [hdy]
    ext ⟨x, z⟩
    simp only [tensorLift_apply, BoundedContinuousFunction.coe_one, Pi.one_apply,
      one_mul]
  have pairing : 0 < dp.mean (tensorLift dy'.eigenvector (1 : K →ᵇ ℝ)) := by
    rw [oneLift]
    exact dp.mean_one_pos
  let dx := descend (C).killedTransition (D).killedTransition PX PY PXY
    (strongFellerTransferOperator_represents C sf)
    (strongFellerTransferOperator_represents D sd) repXY dy' dp pairing
  have posX : ∀ f : K →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ PX f x := by
    intro f hf x
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  have posXY : ∀ f : K × Y →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ PXY f x := by
    intro f hf x
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  let μ := dx.eigenmeasure posX
  let μxy := dp.eigenmeasure posXY
  have : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
  have : IsFiniteMeasure μxy := by dsimp only [μxy]; infer_instance
  have hproduct' : (ν : Measure (K ×ˢ (univ : Set Y))).map e.symm =
      eigenvectorMeasure μxy dp.eigenvector := by
    rw [hproduct]
    exact (ReindexedCanonicalChain.spectralData_product e CD sxy dxy).symm
  have hmap : (ν : Measure (K ×ˢ (univ : Set Y))).map
      (fun z => (LiveProductCoordinates.liveProduct K z).1) =
      eigenvectorMeasure μ dx.eigenvector := by
    have hm := descended_product_eq_first_marginal (C).killedTransition (D).killedTransition
      PX PY PXY (strongFellerTransferOperator_represents C sf)
      (strongFellerTransferOperator_represents D sd) repXY dy' dp pairing μ μxy
      (dx.eigenmeasure_represents posX) (dp.eigenmeasure_represents posXY)
      (dx.eigenvector_nonneg_of_positive posX) (dp.eigenvector_nonneg_of_positive posXY)
    rw [← hproduct', Measure.map_map measurable_fst e.symm.measurable] at hm
    exact hm.symm
  refine ⟨sf, dx, hmap, ?_⟩
  intro x hx
  apply descended_eigenvector_pos (C).killedTransition (D).killedTransition PX PY PXY
    (strongFellerTransferOperator_represents C sf)
    (strongFellerTransferOperator_represents D sd) repXY dy' dp pairing x y
  · exact zero_lt_one
  · exact hpositive (e (x, y)) (by exact ⟨hx, rfl⟩)

end ConditionedStochasticStabilityHyperbolic.Paper.ActualCompactProductGap
