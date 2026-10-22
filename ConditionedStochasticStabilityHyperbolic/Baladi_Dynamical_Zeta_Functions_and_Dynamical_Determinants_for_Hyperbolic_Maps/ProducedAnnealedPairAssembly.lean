module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedPair
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedQuantitativeAnnealedModel
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedQuantitativeAnnealedPair

/-! Proof-preserving assembly of two produced models along the proved
physical inclusion tower. All source and target spaces remain abstract here
so concrete physical model projections need not be normalized repeatedly. -/

public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
open KellerLiverani1999

variable {S H W I V Z : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup I] [NormedSpace ℂ I]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] [MeasurableSpace Z]

@[expose] def assemble
    {i : S →L[ℂ] H} {k : S →L[ℂ] W} {h : H →L[ℂ] I} {j0 : H →L[ℂ] V}
    {law : ℝ≥0 → Measure Z} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {genS : ℝ≥0 → Z → S →L[ℂ] S} {genH : ℝ≥0 → Z → H →L[ℂ] H} {R : ℝ}
    (strong : ProducedAnnealedModel.Data i k law probability genS R)
    (middle : ProducedAnnealedModel.Data h j0 law probability genH R)
    (e : V ≃ₗᵢ[ℂ] W)
    (factor : (e.toLinearIsometry.toContinuousLinearMap.comp j0).comp i = k)
    (compatible : ∀ ε z, i.comp (genS ε z) = (genH ε z).comp i) :
    Data i (e.toLinearIsometry.toContinuousLinearMap.comp j0) law probability genS genH R := by
  let j := e.toLinearIsometry.toContinuousLinearMap.comp j0
  let ss := strong.inputs.changeEmbedding (j.comp i) factor.symm
  let hh := middle.inputs.transportWeak e
  have hs : ∀ ε z, ss.generator ε z = genS ε z := by
    simpa only [ss, ActualAnnealedInputs.changeEmbedding_generator] using strong.generator_eq
  have hm : ∀ ε z, hh.generator ε z = genH ε z := by
    simpa only [hh, ActualAnnealedInputs.transportWeak_generator] using middle.generator_eq
  refine {
    compactS := strong.compactH
    injectiveS := strong.injectiveH
    denseS := strong.denseH
    compactH := middle.compactW.clm_comp e.toLinearIsometry.toContinuousLinearMap
    injectiveH := e.injective.comp middle.injectiveW
    strong := ss
    intermediate := hh
    strong_generator := hs
    intermediate_generator := hm
    compatible := ?_ }
  intro ε
  apply ss.operator_compatibility_of_generators hh i ε
  intro z
  exact (congrArg (fun P => i.comp P) (hs ε z)).trans
    ((compatible ε z).trans (congrArg (fun P => P.comp i) (hm ε z)).symm)

def assembleQuantitative
    {i : S →L[ℂ] H} {k : S →L[ℂ] W} {h : H →L[ℂ] I} {j0 : H →L[ℂ] V}
    {law : ℝ≥0 → Measure Z} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {genS : ℝ≥0 → Z → S →L[ℂ] S} {genH : ℝ≥0 → Z → H →L[ℂ] H}
    {R ρS ρH weakS weakH stepS stepH boundS boundH : ℝ}
    (strong : ProducedAnnealedModel.QuantitativeData i k law probability genS R ρS weakS stepS boundS)
    (middle : ProducedAnnealedModel.QuantitativeData h j0 law probability genH R ρH weakH stepH boundH)
    (e : V ≃ₗᵢ[ℂ] W)
    (factor : (e.toLinearIsometry.toContinuousLinearMap.comp j0).comp i = k)
    (compatible : ∀ ε z, i.comp (genS ε z) = (genH ε z).comp i) :
    QuantitativeData i (e.toLinearIsometry.toContinuousLinearMap.comp j0) law probability
      genS genH R ρS ρH weakS weakH where
  pair := assemble strong.model middle.model e factor compatible
  principalS_eq := (strong.model.inputs.changeEmbedding_principal _ factor.symm).trans strong.principal_eq
  principalH_eq := (middle.model.inputs.transportWeak_principal e).trans middle.principal_eq
  weakRateS_eq := (strong.model.inputs.changeEmbedding_weakRate _ factor.symm).trans strong.weakRate_eq
  weakRateH_eq := (middle.model.inputs.transportWeak_weakRate e).trans middle.weakRate_eq

end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
