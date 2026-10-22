module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldTwoStepModel
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCompatibility
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldRowSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedPairAssembly

/-! The two actual physical exponent models assemble into the exact analytic
pair required by local stochastic stability. Shared function actions derive
all completed/averaged compatibility, and literal lowering aligns W. -/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPairedInputs
open LeanShared DyadicCompletion FiniteRegularTransferRealization KellerLiverani1999

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

variable (a b : m.localization.indices → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
  (ea eb : m.localization.indices → Bool → ℝ)
  (hea : ∀ i j, 0 ≤ ea i j) (heb : ∀ i j, 0 ≤ eb i j)


variable {Noise : Type*} [MeasurableSpace Noise]
  (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
  (noise : ℝ≥0 → Noise → Ω) (R : ℝ)

set_option maxHeartbeats 1600000 in
@[expose] noncomputable def produced
    (rowsS : PhysicalManifoldRowSources.Data (m.twoStepModel a b ha hb ea eb hea heb))
    (rowsH : PhysicalManifoldRowSources.Data (m.intermediateModel a b ha hb ea eb hea heb))
    (strong : ProducedAnnealedModel.Data
      (m.loweredInclusion a ha ea hea)
      (m.loweredInclusion (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
        (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j)))
      law (fun _ => inferInstance)
      (fun ε z => (m.twoStepModel a b ha hb ea eb hea heb).generator (noise ε z)) R)
    (middle : ProducedAnnealedModel.Data
      ((m.intermediateModel a b ha hb ea eb hea heb).loweredInclusion b hb eb heb)
      ((m.intermediateModel a b ha hb ea eb hea heb).loweredInclusion b hb eb heb)
      law (fun _ => inferInstance)
      (fun ε z => (m.intermediateModel a b ha hb ea eb hea heb).generator (noise ε z)) R) :
    ProducedAnnealedPair.Data (m.loweredInclusion a ha ea hea)
      (m.towerSecondInclusion a b ha hb ea eb hea heb) law (fun _ => inferInstance)
      (fun ε z => (m.twoStepModel a b ha hb ea eb hea heb).generator (noise ε z))
      (fun ε z => (m.intermediateModel a b ha hb ea eb hea heb).generator (noise ε z)) R := by
  let ms := m.twoStepModel a b ha hb ea eb hea heb
  let mh := m.intermediateModel a b ha hb ea eb hea heb
  let i := m.loweredInclusion a ha ea hea
  let e := m.towerEquivalence a b ha hb ea eb hea heb
  have hcore : ∀ c, i (coreLift ms.qa c) = coreLift mh.qa c :=
    m.loweredInclusion_core a ha ea hea
  let compat := PhysicalModelCompatibility.compatibleOperators ms mh rfl rfl rfl rfl i hcore
    (operator_core ms.qa (SmoothSupportedManifoldCore.functions V) Reg ms.view ms.view_injective
      ms.realize ms.maps ms.weight ms.coreRegular rowsS.strongBound (rowsS.produced ms).strong)
    (operator_core mh.qa (SmoothSupportedManifoldCore.functions V) Reg mh.view mh.view_injective
      mh.realize mh.maps mh.weight mh.coreRegular rowsH.strongBound (rowsH.produced mh).strong)
  exact ProducedAnnealedPair.assemble strong middle e
    (m.inclusionTower a b ha hb ea eb hea heb).composition
    (fun ε z => compat.generator (noise ε z))

variable {ρS ρH weakS weakH stepS stepH boundS boundH : ℝ}

set_option maxHeartbeats 1600000 in
@[expose] noncomputable def producedQuantitative
    (rowsS : PhysicalManifoldRowSources.Data (m.twoStepModel a b ha hb ea eb hea heb))
    (rowsH : PhysicalManifoldRowSources.Data (m.intermediateModel a b ha hb ea eb hea heb))
    (strong : ProducedAnnealedModel.QuantitativeData
      (m.loweredInclusion a ha ea hea)
      (m.loweredInclusion (fun i => a i + b i) (fun i => add_pos (ha i) (hb i))
        (fun i j => ea i j + eb i j) (fun i j => add_nonneg (hea i j) (heb i j)))
      law (fun _ => inferInstance)
      (fun ε z => (m.twoStepModel a b ha hb ea eb hea heb).generator (noise ε z)) R ρS weakS stepS boundS)
    (middle : ProducedAnnealedModel.QuantitativeData
      ((m.intermediateModel a b ha hb ea eb hea heb).loweredInclusion b hb eb heb)
      ((m.intermediateModel a b ha hb ea eb hea heb).loweredInclusion b hb eb heb)
      law (fun _ => inferInstance)
      (fun ε z => (m.intermediateModel a b ha hb ea eb hea heb).generator (noise ε z)) R ρH weakH stepH boundH) :
    ProducedAnnealedPair.QuantitativeData (m.loweredInclusion a ha ea hea)
      (m.towerSecondInclusion a b ha hb ea eb hea heb) law (fun _ => inferInstance)
      (fun ε z => (m.twoStepModel a b ha hb ea eb hea heb).generator (noise ε z))
      (fun ε z => (m.intermediateModel a b ha hb ea eb hea heb).generator (noise ε z)) R ρS ρH weakS weakH := by
  let ms := m.twoStepModel a b ha hb ea eb hea heb
  let mh := m.intermediateModel a b ha hb ea eb hea heb
  let i := m.loweredInclusion a ha ea hea
  let e := m.towerEquivalence a b ha hb ea eb hea heb
  have hcore : ∀ c, i (coreLift ms.qa c) = coreLift mh.qa c :=
    m.loweredInclusion_core a ha ea hea
  let compat := PhysicalModelCompatibility.compatibleOperators ms mh rfl rfl rfl rfl i hcore
    (operator_core ms.qa (SmoothSupportedManifoldCore.functions V) Reg ms.view ms.view_injective
      ms.realize ms.maps ms.weight ms.coreRegular rowsS.strongBound (rowsS.produced ms).strong)
    (operator_core mh.qa (SmoothSupportedManifoldCore.functions V) Reg mh.view mh.view_injective
      mh.realize mh.maps mh.weight mh.coreRegular rowsH.strongBound (rowsH.produced mh).strong)
  exact ProducedAnnealedPair.assembleQuantitative strong middle e
    (m.inclusionTower a b ha hb ea eb hea heb).composition
    (fun ε z => compat.generator (noise ε z))

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPairedInputs
