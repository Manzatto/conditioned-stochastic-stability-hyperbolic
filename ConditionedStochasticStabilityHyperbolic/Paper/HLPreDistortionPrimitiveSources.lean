module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionPressureSources
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPreControlPrimitiveSources
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPrimitiveSources

/-! Ordinary pre-control HL data produce the complete actual primitive
packet, including random control neighborhoods and strict pressure rates.
No supplied parameterControl, noisy block estimate or compactness field. -/

public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff SchwartzMap BigOperators Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionPrimitiveSources
open LeanShared
variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*}
  [∀ k, NormedAddCommGroup (LocalReg k)] [∀ k, NormedSpace ℂ (LocalReg k)]
  [∀ k, CompleteSpace (LocalReg k)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
variable [MetricSpace Ω]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)
  {Order : Type*} [Fintype Order]


structure Data where
  pressure : HLPreDistortionPressureSources.Data m h
  rows : PhysicalManifoldRowSources.Data m
  distribution : PhysicalManifoldDistributionSources.Data m Order
  noiseRegularity : PhysicalManifoldNoiseSources.Data m

namespace Data
variable (s : Data m h (Order := Order))

@[expose] def classical : HLPreControlPrimitiveSources.Data m h (Order := Order) where
  pressure := s.pressure.constructed m h
  rows := s.rows
  distribution := s.distribution
  noiseRegularity := s.noiseRegularity

@[expose] def primitive : PhysicalManifoldPrimitiveSources.Data m
    (Fiber := fun x => TangentSpace (𝓘(ℝ, E)) x)
    (Params := ChartWordControlFamily.Parameters (fun N => Fin (N + 1) → m.localization.indices))
    (I := fun N => Fin (N + 1) → m.localization.indices) (Order := Order) :=
  (s.classical m h).primitive m h

omit [BorelSpace M] [∀ k, CompleteSpace (LocalReg k)] in
include s in
theorem principal_reference : (s.primitive m h).pressure.T = s.pressure.reference :=
  ((s.classical m h).principal_reference m h).trans (s.pressure.constructed_reference m h)

omit [BorelSpace M] [∀ k, CompleteSpace (LocalReg k)] in
include s in
theorem principal_positive : 0 < (s.primitive m h).pressure.ρ :=
  (s.classical m h).principal_positive m h

omit [BorelSpace M] [∀ k, CompleteSpace (LocalReg k)] in
include s in
theorem principal_lt_pressure : (s.primitive m h).pressure.ρ < Real.exp s.pressure.equilibrium.pressure := by
  have hp := (s.classical m h).principal_lt_pressure m h
  change (s.primitive m h).pressure.ρ < Real.exp (s.pressure.constructed m h).equilibrium.pressure at hp
  simpa only [s.pressure.constructed_equilibrium m h] using hp

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionPrimitiveSources
