module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualLivePrefixNormalizedGap
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualCompactNoiseGap

/-! The produced stabilized global-prefix datum constructs an original
live-prefix gap and its exact first-marginal probability. The original gap,
product eigenmeasure and kernel factorization are conclusions. -/
@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualProductPrefixGapDescent
open LeanShared Paper Paper.RegularNoise Paper.ActualProductRestrictedChain
open ComplexStrongFeller LayerQuasiErgodic
private theorem qem_of_gap
    {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (C : AbsorbingMarkovChains.CanonicalChain Z) (core : Set Z) (ν : ProbabilityMeasure Z)
    (gap : LocalConclusions.NormalizedGap C core ν) : (C).IsQuasiErgodic (ν : Measure Z) := by
  rcases gap with ⟨s, d, eq, _⟩
  let hp : ∀ f : Z →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ strongFellerTransferOperator C s f x :=
    fun f hf x => by rw [strongFellerTransferOperator_represents]; exact integral_nonneg hf
  have qem := QuasiErgodic.strongFeller_rankOne_isQuasiErgodic C s d (d.eigenmeasure hp)
    (d.eigenmeasure_represents hp) (d.eigenvector_nonneg_of_positive hp)
  exact eq.symm ▸ qem

private theorem transport_set
    {Z Ω : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : Z × Ω → Z) (hF : Measurable F)
    {U V : Set Z} [CompactSpace U] [CompactSpace V]
    (hU : MeasurableSet U) (hV : MeasurableSet V) (eq : U = V)
    (w : Z → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
    (Λ : Set Z) (μ : Measure Z)
    (source : ∃ ν : ProbabilityMeasure U,
      LocalConclusions.NormalizedGap
        (RestrictedNoise.chain ρ F hF U hU (fun x => w x.val)
          (hw.comp measurable_subtype_coe) R hR (fun x => bound x.val))
        {x : U | x.val ∈ Λ} ν ∧ (ν : Measure U).map Subtype.val = μ) :
    ∃ ν : ProbabilityMeasure V,
      LocalConclusions.NormalizedGap
        (RestrictedNoise.chain ρ F hF V hV (fun x => w x.val)
          (hw.comp measurable_subtype_coe) R hR (fun x => bound x.val))
        {x : V | x.val ∈ Λ} ν ∧ (ν : Measure V).map Subtype.val = μ := by
  subst V
  exact source

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

/-- Apply the actual product-prefix gap to the original compact live prefix.
The auxiliary constant-weight full-space gap is normalized at one. -/
theorem exists_original_gap
    (nonnegative : ∀ x, 0 ≤ w x) (sf : HasStrongFellerKernel C)
    (νY : ProbabilityMeasure (univ : Set Y))
    (auxiliary : LocalConclusions.NormalizedGap
      (ActualCompactNoiseGap.auxiliaryLocal Pnoise Qnoise L' ε hε hwindow 1 le_rfl) univ νY)
    (sfP : HasStrongFellerKernel CP)
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (RestrictedLayerChain.chain CP (P ×ˢ univ) (hP.measurableSet.prod MeasurableSet.univ))
      (RestrictedLayerChain.strongFeller CP sfP (P ×ˢ univ)
        (hP.measurableSet.prod MeasurableSet.univ))) (1 : ↥(P ×ˢ (univ : Set Y)) →ᵇ ℝ))
    (Λ : Set X) (positive : ∀ z : P ×ˢ (univ : Set Y), z.val.1 ∈ Λ → 0 < d.eigenvector z)
    (y : Y) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
    letI : CompactSpace (P ×ˢ (univ : Set Y)) := isCompact_iff_compactSpace.mp (hP.prod isCompact_univ)
    ∃ ν : ProbabilityMeasure K, LocalConclusions.NormalizedGap C {x : K | x.val ∈ Λ} ν ∧
      (C).IsQuasiErgodic (ν : Measure K) ∧
      (ν : Measure K).map Subtype.val =
        (productMeasure
          (RestrictedLayerChain.chain CP (P ×ˢ univ) (hP.measurableSet.prod MeasurableSet.univ))
          (RestrictedLayerChain.strongFeller CP sfP (P ×ˢ univ)
            (hP.measurableSet.prod MeasurableSet.univ)) d).map (fun z => z.val.1) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp (hP.inter_right hA.isClosed_compl)
  let : CompactSpace (P ×ˢ (univ : Set Y)) := isCompact_iff_compactSpace.mp (hP.prod isCompact_univ)
  let : CompactSpace (univ : Set Y) := isCompact_iff_compactSpace.mp isCompact_univ
  let : CompactSpace (K ×ˢ (univ : Set Y)) := isCompact_iff_compactSpace.mp
    ((hP.inter_right hA.isClosed_compl).prod isCompact_univ)
  have produced := ActualLivePrefixNormalizedGap.exists_normalizedGap
    ((productLaws L L').law ε) (joint ε F G) (measurable_joint ε F G hF hG)
    (P ×ˢ univ) (A ×ˢ univ) (hP.prod isCompact_univ) (hA.prod isOpen_univ)
    (fun z => w z.1) (hw.comp measurable_fst) R hR (fun z => bound z.1) sfP d
    (Λ ×ˢ univ) (fun z hz => positive z hz.1)
  have liveEq : (P ×ˢ (univ : Set Y)) \ (A ×ˢ univ) = K ×ˢ univ :=
    LivePrefixGeometry.live_product P A
  let : CompactSpace ↥((P ×ˢ (univ : Set Y)) \ (A ×ˢ univ)) :=
    isCompact_iff_compactSpace.mp ((hP.prod isCompact_univ).inter_right (hA.prod isOpen_univ).isClosed_compl)
  have transported := transport_set ((productLaws L L').law ε) (joint ε F G)
    (measurable_joint ε F G hF hG)
    ((hP.measurableSet.prod MeasurableSet.univ).diff (hA.prod isOpen_univ).measurableSet)
    ((hK).prod MeasurableSet.univ) liveEq (fun z => w z.1) (hw.comp measurable_fst)
    R hR (fun z => bound z.1) (Λ ×ˢ univ) _ produced
  let νP := Classical.choose transported
  have properties := Classical.choose_spec transported
  have chainEq :
      ActualCompactNoiseGap.compactProduct Pnoise Qnoise L L' ε hε hwindow K hK w hw R 1 hR le_rfl bound =
      RestrictedNoise.chain ((productLaws L L').law ε) (joint ε F G)
        (measurable_joint ε F G hF hG) (K ×ˢ univ) ((hK).prod MeasurableSet.univ)
        (fun z => w z.val.1) ((hw.comp measurable_fst).comp measurable_subtype_coe)
        R hR (fun z => bound z.val.1) := by
    simp only [ActualCompactNoiseGap.compactProduct, productChain, mul_one]
  have pg : LocalConclusions.NormalizedGap
      (ActualCompactNoiseGap.compactProduct Pnoise Qnoise L L' ε hε hwindow K hK w hw R 1 hR le_rfl bound)
      {z | (LiveProductCoordinates.liveProduct K z).1.val ∈ Λ} νP := by
    rw [chainEq]
    have coreEq : ({z : K ×ˢ (univ : Set Y) | z.val ∈ Λ ×ˢ univ} : Set ↥(K ×ˢ univ)) =
        {z | (LiveProductCoordinates.liveProduct K z).1.val ∈ Λ} := by
      ext z
      simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true, LiveProductCoordinates.liveProduct_fst]
    exact Eq.mp (congrArg (fun region : Set ↥(K ×ˢ (univ : Set Y)) =>
      LocalConclusions.NormalizedGap
        (RestrictedNoise.chain ((productLaws L L').law ε) (joint ε F G)
          (measurable_joint ε F G hF hG) (K ×ˢ univ) ((hK).prod MeasurableSet.univ)
          (fun z => w z.val.1) ((hw.comp measurable_fst).comp measurable_subtype_coe)
          R hR (fun z => bound z.val.1)) region νP) coreEq) properties.1
  have slice : LocalConclusions.NormalizedGap
      (ActualCompactNoiseGap.compactProduct Pnoise Qnoise L L' ε hε hwindow K hK w hw R 1 hR le_rfl bound)
      {z | (LiveProductCoordinates.liveProduct K z).1 ∈ {x : K | x.val ∈ Λ} ∧
        (LiveProductCoordinates.liveProduct K z).2 = y} νP := by
    rcases pg with ⟨s, dg, hm, hp⟩
    exact ⟨s, dg, hm, fun z hz => hp z hz.1⟩
  have descended := ActualCompactNoiseGap.normalizedGap Pnoise Qnoise L L' ε hε hwindow
    K hK w hw R 1 hR le_rfl bound nonnegative sf νY auxiliary νP {x : K | x.val ∈ Λ} y slice
  refine ⟨νP.map (fun z => (LiveProductCoordinates.liveProduct K z).1), descended,
    qem_of_gap _ _ _ descended, ?_⟩
  have first := congrArg (fun μ : Measure (X × Y) => μ.map Prod.fst) properties.2
  rw [Measure.map_map measurable_fst measurable_subtype_coe,
    Measure.map_map measurable_fst measurable_subtype_coe] at first
  change ((νP : Measure (K ×ˢ (univ : Set Y))).map
    (fun z => (LiveProductCoordinates.liveProduct K z).1)).map Subtype.val = _
  rw [Measure.map_map measurable_subtype_coe
    ((LiveProductCoordinates.liveProduct K).continuous.measurable.fst)]
  exact first

end ConditionedStochasticStabilityHyperbolic.Global.ActualProductPrefixGapDescent
