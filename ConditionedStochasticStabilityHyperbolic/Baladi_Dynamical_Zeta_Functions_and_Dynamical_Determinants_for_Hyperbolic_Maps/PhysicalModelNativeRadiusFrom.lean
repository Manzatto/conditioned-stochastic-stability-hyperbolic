module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelSubordinateRadius
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelFullTestDistribution
meta import Lean.LibrarySuggestions.Basic

/-! The upper spectral radius bound at the pressure as a generic proposition, with the native
full-test distribution constructed while the model is abstract, so a concrete carrier only supplies
its own data and its statement carries no concrete operator algebra. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelNativeRadiusFrom"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory IsManifold Bundle
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeRadiusUpper
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelAnalytic
  HyperbolicBasicSet ThermodynamicDefinitions

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

/-- Every two-norm estimate of the generator at `a` against a compact operator into `W`, with
essential rate at most `exp P`, bounds the spectral radius by `exp P`. -/
def RadiusFrom (a : Ω) (P : ℝ) (W : Type*) [NormedAddCommGroup W] [NormedSpace ℂ W] : Prop :=
  ∀ (i : m.StrongSpace →L[ℂ] W), IsCompactOperator i → ∀ α R C D : ℝ, 0 ≤ α → 0 ≤ R → 0 ≤ C →
    0 ≤ D → (∀ n x, ‖((m.generator a) ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖) →
    α ≤ Real.exp P → spectralRadius ℂ (m.generator a) ≤ ENNReal.ofReal (Real.exp P)

set_option maxHeartbeats 3200000 in
/-- The upper radius bound at the pressure, with the native full-test distribution. -/
theorem native_radius_upper {L : ℝ} (bound : AnalyticBound m L) (a : Ω)
    {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V)
    (hT : (T : M → M) = m.maps a)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (weightCont : Continuous m.weight) (nonnegative : ∀ x, 0 ≤ m.weight x)
    (positive : ∀ x ∈ Λ, 0 < m.weight x) (supported : Function.support m.weight ⊆ closure V)
    (refData : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (P : ℝ) (pressureP : pressure T (bd.hyperbolic.potential m.weight) Λ = (P : EReal))
    (localBound : PhysicalModelFullTestPairing.LocalPairing m 1)
    (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] :
    RadiusFrom m a P W := by
  intro i hi α R C D hα hR hC hD estimate rate
  have key := radius_upper_at_pressure m bound a bd hT forward inverse weightCont nonnegative
    positive supported refData volume P pressureP
    (PhysicalModelFullTestDistribution.aFull m refData one_pos le_rfl localBound)
    (fun t => BoundedContinuousFunction.mkOfCompact
      ⟨NativeFullHolderTests.view 1 le_rfl t,
        PhysicalModelFullTestDistribution.view_continuous (E := E) le_rfl t⟩)
    (fun c t => PhysicalModelFullTestDistribution.aFull_core m refData one_pos le_rfl
      localBound c t)
    (PhysicalModelFullTestDistribution.aFull_injective m refData one_pos le_rfl localBound)
    physReg hphys i hi α R C D hα hR hC hD estimate rate
  exact key

end ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeRadiusUpper
