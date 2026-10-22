module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalLayerModels
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise
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
namespace ConditionedStochasticStabilityHyperbolic.Paper.RepresentedLayerModel
open LeanShared LeanShared.DyadicCompletion LeanShared.CompletedChartPairTransfer
open LeanShared.FiniteRegularTransferRealization

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
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


variable {ι : Type*} [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ} (F : RegularNoise.Maps (E := E) (ι := ι) T r)
  (p : RegularNoise.Representation F Ω m.maps)


/-- The literal Whitney representation produces the actual analytic model.
Only ordinary row/distribution/pressure sources and numeric normalization are
inputs. No noise-dependent gap, compact embedding or operator estimate is
supplied. -/
@[expose] def source
    (primitive : PhysicalManifoldPrimitiveSources.Data m
      (Fiber := Fiber) (Params := Params) (I := I) (Order := Order))
    (reference : primitive.pressure.T = p.reference)
    (weakRate R : ℝ) (hρ : 0 < primitive.pressure.ρ)
    (hweak : primitive.pressure.ρ < weakRate)
    (hone : primitive.rows.weakBound ≤ weakRate) (hR : 1 ≤ R)
    (hρR : primitive.pressure.ρ < R) :
    PhysicalLayerModels.Data m (Fiber := Fiber) (Params := Params)
      (I := I) (Order := Order) (Noise := RegularNoise.FixedControl (ι := ι)) R where
  primitive := primitive
  noise := p.fixedParameters
  noise_continuous := p.fixedParameters_continuous
  noiseConstant := p.constant
  close := by
    intro ε z
    rw [reference]
    exact p.fixedParameters_close ε z
  weakRate := weakRate
  principal_positive := hρ
  principal_lt_weak := hweak
  weak_oneStep := hone
  scale_ge_one := hR
  principal_lt_scale := hρR

end ConditionedStochasticStabilityHyperbolic.Paper.RepresentedLayerModel
