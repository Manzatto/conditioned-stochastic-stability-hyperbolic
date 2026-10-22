module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualProductPrefixAmbientGap
public import ConditionedStochasticStabilityHyperbolic.Global.LiveToPrefixGap
public import ConditionedStochasticStabilityHyperbolic.Global.PrefixDataTransport

/-! Produced stabilized prefix data construct the original compact-prefix gap,
with the same first marginal. No endpoint gap or eigenmeasure is assumed. -/
@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.RepresentedProductPrefixGap
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
    (nonnegative : ∀ x, 0 ≤ w x)
    (original : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel original)
    (actualOriginal : original = C0)
    (stabilized : AbsorbingMarkovChains.CanonicalChain (X × Y)) (sfP : HasStrongFellerKernel stabilized)
    (actualProduct : stabilized = CP)
    (Q : Set (X × Y)) [CompactSpace Q] (hQ : MeasurableSet Q) (actualPrefix : Q = P ×ˢ univ)
    (νY : ProbabilityMeasure (univ : Set Y))
    (auxiliary : LocalConclusions.NormalizedGap
      (ActualCompactNoiseGap.auxiliaryLocal Pnoise Qnoise L' ε hε hwindow 1 le_rfl) univ νY)
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (RestrictedLayerChain.chain stabilized Q hQ)
      (RestrictedLayerChain.strongFeller stabilized sfP Q hQ)) (1 : Q →ᵇ ℝ))
    (Λ : Set X) (hΛlive : Λ ⊆ Aᶜ)
    (positive : ∀ z : Q, z.val ∈ Λ ×ˢ univ → 0 < d.eigenvector z)
    (y : Y) :
    letI : CompactSpace P := isCompact_iff_compactSpace.mp hP
    ∃ dp : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (RestrictedLayerChain.chain original P hP.measurableSet)
      (RestrictedLayerChain.strongFeller original sf P hP.measurableSet)) (1 : P →ᵇ ℝ),
      (∀ x : P, x.val ∈ Λ → 0 < dp.eigenvector x) ∧
      (productMeasure (RestrictedLayerChain.chain original P hP.measurableSet)
        (RestrictedLayerChain.strongFeller original sf P hP.measurableSet) dp).map Subtype.val =
        (productMeasure (RestrictedLayerChain.chain stabilized Q hQ)
          (RestrictedLayerChain.strongFeller stabilized sfP Q hQ) d).map (fun z => z.val.1) := by
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let : CompactSpace (P ×ˢ (univ : Set Y)) := isCompact_iff_compactSpace.mp (hP.prod isCompact_univ)
  have sfRaw : HasStrongFellerKernel C0 := actualOriginal ▸ sf
  have sfProdRaw : HasStrongFellerKernel CP := actualProduct ▸ sfP
  have rawProduct := PrefixDataTransport.transport sfP sfProdRaw actualProduct
    hQ (hP.measurableSet.prod MeasurableSet.univ) actualPrefix d (Λ ×ˢ univ) positive
  let dr := Classical.choose rawProduct
  have hr := Classical.choose_spec rawProduct
  have descended := ActualProductPrefixAmbientGap.exists_original_prefix_gap
    Pnoise Qnoise L L' ε hε hwindow P A hP hA w hw R hR bound nonnegative
    sfRaw νY auxiliary sfProdRaw dr Λ hΛlive (fun z hz => hr.1 z ⟨hz, mem_univ _⟩) y
  let dp := Classical.choose descended
  have hp := Classical.choose_spec descended
  have represented := PrefixDataTransport.transport sfRaw sf actualOriginal.symm
    hP.measurableSet hP.measurableSet rfl dp Λ hp.1
  let result := Classical.choose represented
  have resultProperties := Classical.choose_spec represented
  refine ⟨result, resultProperties.1, resultProperties.2.trans (hp.2.trans ?_)⟩
  have first := congrArg (fun μ : Measure (X × Y) => μ.map Prod.fst) hr.2
  rw [Measure.map_map measurable_fst measurable_subtype_coe,
    Measure.map_map measurable_fst measurable_subtype_coe] at first
  exact first

end ConditionedStochasticStabilityHyperbolic.Global.RepresentedProductPrefixGap
