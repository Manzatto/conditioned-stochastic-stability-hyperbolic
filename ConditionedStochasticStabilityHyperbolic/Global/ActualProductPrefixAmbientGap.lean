module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualProductPrefixGapDescent
public import ConditionedStochasticStabilityHyperbolic.Global.LiveToPrefixGap

/-! Produced stabilized prefix data construct the original compact-prefix gap,
with the same first marginal. No endpoint gap or eigenmeasure is assumed. -/
@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualProductPrefixAmbientGap
open LeanShared Paper Paper.RegularNoise Paper.ActualProductRestrictedChain
open ComplexStrongFeller LayerQuasiErgodic
variable {X Y E H ι κ : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y] [ChartedSpace E X] [ChartedSpace H Y]
  {T : X ≃ₜ X} {T' : Y ≃ₜ Y} {r : ℝ}
  (Pnoise : Maps (E := E) (ι := ι) T r) (Qnoise : Maps (E := H) (ι := κ) T' r)
  (L : Laws (ι := ι)) (L' : Laws (ι := κ))
  (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ min Pnoise.window Qnoise.window)
  (P A : Set X) (hP : IsCompact P) (hA : IsOpen A)
  (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)

set_option quotPrecheck false in
local notation "F" => actualMap Pnoise ε
set_option quotPrecheck false in
local notation "G" => actualMap Qnoise ε
set_option quotPrecheck false in
local notation "hF" => actualMap_measurable Pnoise ε hε (le_min_iff.mp hwindow).1
set_option quotPrecheck false in
local notation "hG" => actualMap_measurable Qnoise ε hε (le_min_iff.mp hwindow).2
set_option quotPrecheck false in
local notation "K" => ((P \ A) : Set X)
set_option quotPrecheck false in
local notation "hK" => hP.measurableSet.diff hA.measurableSet
set_option quotPrecheck false in
local notation "CP" => NoiseKernel.chain ((productLaws L L').law ε) (joint ε F G)
  (measurable_joint ε F G hF hG) (A ×ˢ (univ : Set Y))ᶜ
  (hA.prod isOpen_univ).measurableSet.compl (fun z => w z.1) (hw.comp measurable_fst)
  R hR (fun z => bound z.1)
set_option quotPrecheck false in
local notation "C" => ActualCompactNoiseGap.original Pnoise Qnoise L ε hε hwindow K hK w hw R hR bound

local instance productLawProbability : IsProbabilityMeasure ((productLaws L L').law ε) :=
  (productLaws L L').probability ε

local instance compactAuxiliary : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ


set_option quotPrecheck false in
local notation "C0" => NoiseKernel.chain (L.law ε) F hF Aᶜ hA.measurableSet.compl w hw R hR bound
set_option quotPrecheck false in
local notation "C0P" => RestrictedLayerChain.chain C0 P hP.measurableSet

 theorem exists_original_prefix_gap
    (nonnegative : ∀ x, 0 ≤ w x) (sf : HasStrongFellerKernel C0)
    (νY : ProbabilityMeasure (univ : Set Y))
    (auxiliary : LocalConclusions.NormalizedGap
      (ActualCompactNoiseGap.auxiliaryLocal Pnoise Qnoise L' ε hε hwindow 1 le_rfl) univ νY)
    (sfP : HasStrongFellerKernel CP)
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (RestrictedLayerChain.chain CP (P ×ˢ univ) (hP.measurableSet.prod MeasurableSet.univ))
      (RestrictedLayerChain.strongFeller CP sfP (P ×ˢ univ)
        (hP.measurableSet.prod MeasurableSet.univ))) (1 : ↥(P ×ˢ (univ : Set Y)) →ᵇ ℝ))
    (Λ : Set X) (hΛlive : Λ ⊆ Aᶜ)
    (positive : ∀ z : P ×ˢ (univ : Set Y), z.val.1 ∈ Λ → 0 < d.eigenvector z)
    (y : Y) :
    letI : CompactSpace P := isCompact_iff_compactSpace.mp hP
    letI : CompactSpace (P ×ˢ (univ : Set Y)) := isCompact_iff_compactSpace.mp (hP.prod isCompact_univ)
    ∃ dp : RankOneSpectralData (transferOperator (𝕜 := ℝ) C0P
      (RestrictedLayerChain.strongFeller C0 sf P hP.measurableSet)) (1 : P →ᵇ ℝ),
      (∀ x : P, x.val ∈ Λ → 0 < dp.eigenvector x) ∧
      (productMeasure C0P (RestrictedLayerChain.strongFeller C0 sf P hP.measurableSet) dp).map Subtype.val =
        (productMeasure
          (RestrictedLayerChain.chain CP (P ×ˢ univ) (hP.measurableSet.prod MeasurableSet.univ))
          (RestrictedLayerChain.strongFeller CP sfP (P ×ˢ univ)
            (hP.measurableSet.prod MeasurableSet.univ)) d).map (fun z => z.val.1) := by
  let : IsProbabilityMeasure (L.law ε) := L.probability ε
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let : CompactSpace K := isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
  let : CompactSpace (P ×ˢ (univ : Set Y)) := isCompact_iff_compactSpace.mp (hP.prod isCompact_univ)
  have actual := LiteralNoiseLiveChain.actual_local_chain_eq_global_restriction
    (L.law ε) F hF Aᶜ K hA.measurableSet.compl hK (fun _ hx => hx.2) w hw R hR bound
  have sfLive : HasStrongFellerKernel C := by
    change HasStrongFellerKernel (RestrictedNoise.chain (L.law ε) F hF K hK
      (fun x : K => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => bound x.val))
    rw [actual]
    exact RestrictedLayerChain.strongFeller C0 sf K hK
  have descended := ActualProductPrefixGapDescent.exists_original_gap
    Pnoise Qnoise L L' ε hε hwindow P A hP hA w hw R hR bound
    nonnegative sfLive νY auxiliary sfP d Λ positive y
  let ν := Classical.choose descended
  have hp := Classical.choose_spec descended
  have gap : LocalConclusions.NormalizedGap
      (RestrictedLayerChain.chain C0 K hK) {x : K | x.val ∈ Λ} ν := actual ▸ hp.1
  have extended := LiveToPrefixGap.exists_prefix_gap P A hP hA C0 sf
    (ActualLivePrefixNormalizedGap.zero_absorbing (L.law ε) F hF A hA w hw R hR bound)
    Λ hΛlive ν gap
  let dp := Classical.choose extended
  have hd := Classical.choose_spec extended
  exact ⟨dp, hd.1, hd.2.trans hp.2.2⟩

end ConditionedStochasticStabilityHyperbolic.Global.ActualProductPrefixAmbientGap
