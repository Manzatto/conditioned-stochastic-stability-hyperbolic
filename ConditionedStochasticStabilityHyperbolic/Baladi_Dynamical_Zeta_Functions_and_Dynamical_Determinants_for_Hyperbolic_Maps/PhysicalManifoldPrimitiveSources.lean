module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldRowSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedTransport
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldLoweredInclusion
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldDistributionSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPressureSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldNoiseSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedFiniteRegularAnnealedRates
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedQuantitativeAnnealedModel

/-! Primitive classical sources construct actual physical manifold KL inputs.
All completion spaces, compact inclusions, actual weighted generators, robust
pressure blocks, evaluated-core measurability and mixed-norm convergence are
produced internally. The law is allowed to vary with the noise scale. -/

public noncomputable section
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff SchwartzMap BigOperators Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPrimitiveSources
open LeanShared LeanShared.DyadicCompletion LeanShared.CompletedChartPairTransfer
open LeanShared.FiniteRegularTransferRealization

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*}
  [∀ k, NormedAddCommGroup (LocalReg k)] [∀ k, NormedSpace ℂ (LocalReg k)]
  [∀ k, CompleteSpace (LocalReg k)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)




variable [MetricSpace Ω]
  {Fiber : M → Type*} [∀ x, NormedAddCommGroup (Fiber x)]
  [∀ x, InnerProductSpace ℝ (Fiber x)] [∀ x, FiniteDimensional ℝ (Fiber x)]
  {Params : Type*} {I : ℕ → Type*} {Order : Type*} [Fintype Order]

structure Data where
  rows : PhysicalManifoldRowSources.Data m
  distribution : PhysicalManifoldDistributionSources.Data m Order
  pressure : PhysicalManifoldPressureSources.Data m (Fiber := Fiber) (Params := Params) (I := I)
  noiseRegularity : PhysicalManifoldNoiseSources.Data m
  reference : noiseRegularity.T = pressure.T
  exponents : ∀ i, m.exponent i true = pressure.t ∧ m.exponent i false = pressure.s

namespace Data
variable (p : Data m (Fiber := Fiber) (Params := Params) (I := I) (Order := Order))

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
omit [MetricSpace Ω] in
private theorem inclusionHCore (c : PhysicalManifoldModel.Core (E := E) V) :
    m.inclusionH (coreLift m.qa c) = coreLift m.qH c :=
  ManifoldCompactEmbedding.embedding_core m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossH_positive m.extraH m.extraH_nonnegative c

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
omit [MetricSpace Ω] in
private theorem inclusionWCore (c : PhysicalManifoldModel.Core (E := E) V) :
    m.inclusionW (coreLift m.qa c) = coreLift m.qW c :=
  ManifoldCompactEmbedding.embedding_core m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative c

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
omit [MetricSpace Ω] in
private theorem weakWCoreMap : CompletedChartPairTransfer.coreMap
    m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
    (SmoothSupportedManifoldCore.smooth V) m.weakLocalBlocksW = m.qW :=
  ManifoldMicrolocalWeakCore.rowWeakCore_eq m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative

/- The actual canonical strong-to-intermediate map is compact and injective. -/
include p in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem compact_injective_H : IsCompactOperator m.inclusionH ∧ Function.Injective m.inclusionH :=
  ManifoldCompactEmbedding.compact_injective m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossH_positive m.extraH m.extraH_nonnegative
    p.distribution.words p.distribution.compact_support p.distribution.cutoff
    p.distribution.supported p.distribution.one p.distribution.pairing
    p.distribution.constant p.distribution.constant_nonnegative p.distribution.bound p.distribution.core

/- The actual canonical strong-to-weak map is compact and injective. -/
include p in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem compact_injective_W : IsCompactOperator m.inclusionW ∧ Function.Injective m.inclusionW :=
  ManifoldCompactEmbedding.compact_injective m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative
    p.distribution.words p.distribution.compact_support p.distribution.cutoff
    p.distribution.supported p.distribution.one p.distribution.pairing
    p.distribution.constant p.distribution.constant_nonnegative p.distribution.bound p.distribution.core

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
omit [MetricSpace Ω] in
private theorem denseH : DenseRange m.inclusionH :=
  ManifoldMicrolocalWeakCore.embedding_dense m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossH_positive m.extraH m.extraH_nonnegative

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
omit [MetricSpace Ω] in
private theorem denseW : DenseRange m.inclusionW :=
  ManifoldMicrolocalWeakCore.embedding_dense m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative

set_option maxHeartbeats 1600000 in
/- No global noisy word bound, compactness or mixed-norm convergence is a
primitive source. All arise from actual chart blocks and ordinary sources. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] in
private theorem exists_actual_inputs
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] [SecondCountableTopology Z]
    (noise : ℝ≥0 → Z → Ω) (continuous_noise : ∀ ε, Continuous (noise ε))
    (noiseConstant : ℝ)
    (close : ∀ ε z, dist (noise ε z) p.pressure.T ≤ noiseConstant * (ε : ℝ))
    (law : ℝ≥0 → Measure Z) [∀ ε, IsProbabilityMeasure (law ε)]
    (weakRate scale : ℝ) (hρ : 0 < p.pressure.ρ) (hrate : p.pressure.ρ < weakRate)
    (hweakRate : p.rows.weakBound ≤ weakRate) (hscale : 1 ≤ scale) (hρscale : p.pressure.ρ < scale) :
    ∃ inputs : KellerLiverani1999.ActualAnnealedInputs law
        (fun ε => (inferInstance : IsProbabilityMeasure (law ε))) m.inclusionW scale,
      (∀ ε z, inputs.generator ε z = m.generator (noise ε z)) ∧
      inputs.principal = p.pressure.ρ ∧ inputs.weakRate = weakRate ∧
      inputs.weakOneStep = p.rows.weakBound ∧ inputs.operatorBound = p.rows.strongBound := by
  have limit : ∀ c, Tendsto
      (fun a => regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
        m.maps m.weight m.coreRegular a c) (𝓝 p.pressure.T)
      (𝓝 (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
        m.maps m.weight m.coreRegular p.pressure.T c)) := by
    intro c
    simpa only [p.reference] using p.noiseRegularity.core_tendsto m c
  let density := fun N => IntrinsicPrincipalDensity.density m.maps Fiber p.pressure.differential
    p.pressure.envelope p.pressure.stable p.pressure.unstable N p.pressure.t p.pressure.s
  have continuous : ∀ N k, ContinuousOn (density N) (p.pressure.chart N k) :=
    fun N k => ContinuousIntrinsicPrincipalDensity.continuousOn_density m.maps Fiber
      p.pressure.differential p.pressure.envelope p.pressure.stable p.pressure.unstable
      N p.pressure.t p.pressure.s p.pressure.ht p.pressure.hs (p.pressure.chart N k)
      (p.pressure.weight_continuous N k) (p.pressure.jacobian_continuous N k)
      (p.pressure.stable_continuous N k) (p.pressure.inverse_continuous N k)
  let weakAmbient : m.StrongSpace →L[ℂ]
      (∀ k : m.localization.indices, DyadicCompletion.closedCore (DyadicCompletion.finalCore
        (m.localBlocks k) (m.lossW k) (m.lossW_positive k) (m.extraW k) (m.extraW_nonnegative k))) :=
    (closedCore m.qW).subtypeL.comp m.inclusionW
  have weakAmbient_core : ∀ c, weakAmbient (coreLift m.qa c) =
      CompletedMicrolocalEstimate.weakCore m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
        m.weakLocalBlocksW c := by
    intro c
    exact (congrArg (fun z : closedCore m.qW =>
      z.val)
      (inclusionWCore m c)).trans
      (congrArg (fun q => q c) (weakWCoreMap m).symm)
  classical
  have robust :=
    ManifoldIntrinsicBlock.exists_robust_completed_block
      (E := E) (M := M) (AtlasIndex := AtlasIndex)
      (Core := PhysicalManifoldModel.Core (E := E) V) (Reg := Reg) (S := S)
      (LocalReg := fun k : m.localization.indices => LocalReg k.val)
      (B := fun k => DyadicCompletion.BlockSpace
        (F := GraphLeafNorm.AmbientFamilySpace μ (m.leaves k)) (S := Bool))
      (W := fun k => DyadicCompletion.closedCore (DyadicCompletion.finalCore
        (m.localBlocks k) (m.lossW k) (m.lossW_positive k) (m.extraW k) (m.extraW_nonnegative k)))
      (Ω := Ω) (Params := Params) (I := I)
      m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      m.view m.regularCore m.regularCore_dense m.view_core m.evaluate m.evaluation
      m.localView m.localView_injective m.localCore m.localCore_dense m.localView_core
      m.localEvaluate m.localEvaluation m.coordinateConstant m.coordinateBound
      m.localBlocks m.blockConstant m.blockBound m.core_zero_outside m.view_injective
      m.maps m.weight m.invariant m.coreRegular m.regularConstant m.regularBound
      p.rows.strongBound (p.rows.produced m).strong m.weakLocalBlocksW
      p.pressure.T p.pressure.K p.pressure.hK density
      p.pressure.chart p.pressure.hchart p.pressure.surviving p.pressure.closed p.pressure.cover
      continuous p.pressure.bounded p.pressure.parameters p.pressure.parameterControl
      p.pressure.valid p.pressure.validNeighborhood p.pressure.Qpressure p.pressure.Cmic
      p.pressure.Cchart p.pressure.ρ p.pressure.hCmic p.pressure.hCchart p.pressure.positive
      p.pressure.slack p.pressure.pressure weakAmbient weakAmbient_core
      p.pressure.capture p.pressure.capture_open p.pressure.capture_reference
      p.pressure.pairMember p.pressure.principal p.pressure.remainder p.pressure.nonneg p.pressure.source
  let N := Classical.choose robust
  have nSpec := Classical.choose_spec robust
  have hN : 0 < N := nSpec.1
  let O := Classical.choose nSpec.2
  have openSpec := Classical.choose_spec nSpec.2
  have hO : IsOpen O := openSpec.1
  have hTO : p.pressure.T ∈ O := openSpec.2.1
  let B := Classical.choose openSpec.2.2
  have boundSpec := Classical.choose_spec openSpec.2.2
  have hB : 0 ≤ B := boundSpec.1
  have block := boundSpec.2
  have actualBlock : ∀ word : Fin N → Ω, (∀ k, word k ∈ O) → ∀ x : m.StrongSpace,
      ‖LeanShared.FiniteBlockAnnealedEstimates.listWord m.generator (List.ofFn word) x‖ ≤
        p.pressure.ρ ^ N * ‖x‖ + B * ‖m.inclusionW x‖ := by
    intro word hw x
    exact block word hw x
  have annealed := ConstructedFiniteRegularAnnealedRates.exists_inputs_of_regular_density
    (X := M) (G := Ω) (Ω := Z) (Core := PhysicalManifoldModel.Core (E := E) V)
    (VS := ∀ k : m.localization.indices, DyadicCompletion.BlockSpace
      (F := GraphLeafNorm.AmbientFamilySpace μ (m.leaves k)) (S := Bool))
    (VH := ∀ k : m.localization.indices, DyadicCompletion.closedCore (DyadicCompletion.finalCore
      (m.localBlocks k) (m.lossH k) (m.lossH_positive k) (m.extraH k) (m.extraH_nonnegative k)))
    (VW := ∀ k : m.localization.indices, DyadicCompletion.closedCore (DyadicCompletion.finalCore
      (m.localBlocks k) (m.lossW k) (m.lossW_positive k) (m.extraW k) (m.extraW_nonnegative k)))
    (High := Reg) (Low := Reg)
    m.qa m.qH m.qW (SmoothSupportedManifoldCore.functions V)
    m.view m.view_injective m.view m.view_injective (ContinuousLinearMap.id ℂ Reg) (fun _ => rfl)
    m.maps m.weight m.coreRegular m.coreRegular m.realize (PhysicalManifoldRowSources.weakRealize m)
    m.inclusionH (compact_injective_H m p).1 m.inclusionW (inclusionHCore m) (inclusionWCore m)
    m.regularCore m.regularCore_dense m.realize_core (p.rows.produced m).core
    p.rows.strongBound p.rows.rectangularBound (p.rows.strongBound_nonnegative m)
    (p.rows.rectangularBound_nonnegative m) (p.rows.produced m).strong (p.rows.produced m).rectangular
    p.pressure.T limit noise noiseConstant close law
    (p.noiseRegularity.noise_core_continuous m noise continuous_noise)
    p.rows.weakBound (p.rows.weakBound_nonnegative m) (p.rows.produced m).weak
    N hN p.pressure.ρ weakRate scale hρ hrate hweakRate hscale hρscale
    O (hO.mem_nhds hTO) B hB actualBlock
  exact annealed

/- The public result is a generic produced bundle; all nested physical norm
proofs stay private while consumers receive proved inclusion properties. -/
set_option maxHeartbeats 1600000 in
private noncomputable def canonicalModel
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] [SecondCountableTopology Z]
    (noise : ℝ≥0 → Z → Ω) (continuous_noise : ∀ ε, Continuous (noise ε))
    (noiseConstant : ℝ)
    (close : ∀ ε z, dist (noise ε z) p.pressure.T ≤ noiseConstant * (ε : ℝ))
    (law : ℝ≥0 → Measure Z) [∀ ε, IsProbabilityMeasure (law ε)]
    (weakRate scale : ℝ) (hρ : 0 < p.pressure.ρ) (hrate : p.pressure.ρ < weakRate)
    (hweakRate : p.rows.weakBound ≤ weakRate) (hscale : 1 ≤ scale) (hρscale : p.pressure.ρ < scale) :
    ProducedAnnealedModel.QuantitativeData m.inclusionH m.inclusionW law
      (fun ε => (inferInstance : IsProbabilityMeasure (law ε)))
      (fun ε z => m.generator (noise ε z)) scale
      p.pressure.ρ weakRate p.rows.weakBound p.rows.strongBound := by
  let h := exists_actual_inputs m p noise continuous_noise noiseConstant close law
    weakRate scale hρ hrate hweakRate hscale hρscale
  exact {
    model := {
      compactH := (compact_injective_H m p).1
      injectiveH := (compact_injective_H m p).2
      denseH := denseH m
      compactW := (compact_injective_W m p).1
      injectiveW := (compact_injective_W m p).2
      denseW := denseW m
      inputs := Classical.choose h
      generator_eq := (Classical.choose_spec h).1
    }
    principal_eq := (Classical.choose_spec h).2.1
    weakRate_eq := (Classical.choose_spec h).2.2.1
    weakOneStep_eq := (Classical.choose_spec h).2.2.2.1
    operatorBound_eq := (Classical.choose_spec h).2.2.2.2
  }

/- The exported model uses genuine fresh physical lower-exponent completions.
All canonical nested-space proofs and transport stay inside the construction. -/
set_option maxHeartbeats 1600000 in
noncomputable def actualModel
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] [SecondCountableTopology Z]
    (noise : ℝ≥0 → Z → Ω) (continuous_noise : ∀ ε, Continuous (noise ε))
    (noiseConstant : ℝ)
    (close : ∀ ε z, dist (noise ε z) p.pressure.T ≤ noiseConstant * (ε : ℝ))
    (law : ℝ≥0 → Measure Z) [∀ ε, IsProbabilityMeasure (law ε)]
    (weakRate scale : ℝ) (hρ : 0 < p.pressure.ρ) (hrate : p.pressure.ρ < weakRate)
    (hweakRate : p.rows.weakBound ≤ weakRate) (hscale : 1 ≤ scale) (hρscale : p.pressure.ρ < scale) :
    ProducedAnnealedModel.QuantitativeData
      (m.loweredInclusion m.lossH m.lossH_positive m.extraH m.extraH_nonnegative)
      (m.loweredInclusion m.lossW m.lossW_positive m.extraW m.extraW_nonnegative) law
      (fun ε => (inferInstance : IsProbabilityMeasure (law ε)))
      (fun ε z => m.generator (noise ε z)) scale
      p.pressure.ρ weakRate p.rows.weakBound p.rows.strongBound := by
  exact (canonicalModel m p noise continuous_noise noiseConstant close law
    weakRate scale hρ hrate hweakRate hscale hρscale).transport
      (m.loweredEquivalence m.lossH m.lossH_positive m.extraH m.extraH_nonnegative)
      (m.loweredEquivalence m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPrimitiveSources
