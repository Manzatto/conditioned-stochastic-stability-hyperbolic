module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalPressureSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPrimitiveSources

/-! Faithful HL ordinary sources produce the analytic primitive packet.
The actual tangent/cylinder/envelope pressure construction selects its strict
rate internally. Ordinary local rows, distribution order and little-Cu
interpolation are separate cited background. No primitive packet, completed
compactness, perturbation limit or noisy spectral conclusion is a field.
This is the saddle source branch identified by HLPhysicalPressureSources. -/

public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff SchwartzMap BigOperators Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLPrimitiveSources
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
  {Params : Type*} {Order : Type*} [Fintype Order]


structure Data where
  pressure : HLPhysicalPressureSources.Data m h (Params := Params)
  rows : PhysicalManifoldRowSources.Data m
  distribution : PhysicalManifoldDistributionSources.Data m Order
  noiseRegularity : PhysicalManifoldNoiseSources.Data m

namespace Data
variable (s : Data m h (Params := Params) (Order := Order))

@[expose] noncomputable def selected : s.pressure.Selected m h := s.pressure.selected m h

@[expose] noncomputable def primitive : PhysicalManifoldPrimitiveSources.Data m
    (Fiber := fun x => TangentSpace (𝓘(ℝ, E)) x) (Params := Params)
    (I := fun N => Fin (N + 1) → m.localization.indices) (Order := Order) where
  rows := s.rows
  distribution := s.distribution
  pressure := (s.selected m h).sources m h s.pressure
  noiseRegularity := { s.noiseRegularity with T := ((s.selected m h).sources m h s.pressure).T }
  reference := rfl
  exponents := (s.selected m h).sources_exponents m h s.pressure

omit [BorelSpace M] [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] in
include s in
theorem principal_reference : (s.primitive m h).pressure.T = s.pressure.reference :=
  (s.selected m h).sources_reference m h s.pressure

omit [BorelSpace M] [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] in
include s in
theorem principal_positive : 0 < (s.primitive m h).pressure.ρ :=
  (s.selected m h).sources_positive m h s.pressure

omit [BorelSpace M] [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] in
include s in
theorem principal_lt_pressure : (s.primitive m h).pressure.ρ < Real.exp s.pressure.equilibrium.pressure :=
  (s.selected m h).sources_below_pressure m h s.pressure

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.HLPrimitiveSources
