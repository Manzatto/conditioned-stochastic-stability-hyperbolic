module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPrimitiveSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedZero
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
namespace ConditionedStochasticStabilityHyperbolic.PhysicalLayerModels
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


variable {Noise : Type*} [TopologicalSpace Noise] [MeasurableSpace Noise]
  [OpensMeasurableSpace Noise] [SecondCountableTopology Noise]

/-- Primitive physical model and ordinary numerical normalization choices.
There is no analytic input bundle, compactness, spectral comparison, QEM or
weak-limit field. Each retained layer may have its own leaf dimension. -/
structure Data (R : ℝ) where
  primitive : PhysicalManifoldPrimitiveSources.Data m (Fiber := Fiber) (Params := Params) (I := I) (Order := Order)
  noise : ℝ≥0 → Noise → Ω
  noise_continuous : ∀ ε, Continuous (noise ε)
  noiseConstant : ℝ
  close : ∀ ε z, dist (noise ε z) primitive.pressure.T ≤ noiseConstant * (ε : ℝ)
  weakRate : ℝ
  principal_positive : 0 < primitive.pressure.ρ
  principal_lt_weak : primitive.pressure.ρ < weakRate
  weak_oneStep : primitive.rows.weakBound ≤ weakRate
  scale_ge_one : 1 ≤ R
  principal_lt_scale : primitive.pressure.ρ < R

namespace Data
variable {R : ℝ} (d : Data m (Fiber := Fiber) (Params := Params) (I := I) (Order := Order) (Noise := Noise) R)

/-- The actual varying-law analytic model, including compact and injective
physical embeddings and the actual generator identity, is produced. -/
def produce (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)] :
    ProducedAnnealedModel.QuantitativeData
      (m.loweredInclusion m.lossH m.lossH_positive m.extraH m.extraH_nonnegative)
      (m.loweredInclusion m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)
      law (fun _ => inferInstance) (fun ε z => m.generator (d.noise ε z)) R
      d.primitive.pressure.ρ d.weakRate d.primitive.rows.weakBound d.primitive.rows.strongBound := by
  have produced := d.primitive.actualModel m d.noise d.noise_continuous d.noiseConstant d.close law
    d.weakRate R d.principal_positive d.principal_lt_weak d.weak_oneStep d.scale_ge_one d.principal_lt_scale
  exact produced

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] [MeasurableSpace Noise] [OpensMeasurableSpace Noise]
  [SecondCountableTopology Noise] in
/-- The parameter representation is exactly deterministic at zero scale. -/
theorem noise_zero (z : Noise) : d.noise 0 z = d.primitive.pressure.T := by
  apply dist_le_zero.mp
  simpa only [NNReal.coe_zero, mul_zero] using d.close 0 z


omit [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- The raw zero-scale operator is the deterministic physical generator,
independently of the probability law chosen at zero. -/
theorem raw_zero (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)] :
    (R : ℂ) • (d.produce m law).model.inputs.operator 0 = m.generator d.primitive.pressure.T := by
  have hR : R ≠ 0 := (zero_lt_one.trans_le d.scale_ge_one).ne'
  apply (d.produce m law).model.inputs.raw_zero_of_constant_generators hR
  intro z
  exact ((d.produce m law).model.generator_eq 0 z).trans (congrArg m.generator (d.noise_zero m z))

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalLayerModels
