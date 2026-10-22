module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelProductTangent
public import LeanShared.Dynamics.EquilibriumTangentIdentification
public import LeanShared.Dynamics.HyperbolicExpansivity
public import LeanShared.Dynamics.HyperbolicPotentialContinuity
meta import Lean.LibrarySuggestions.Basic

/-! The spectral product is the equilibrium state. For every smooth real `ψ`, the pressure
supporting inequality `t · Re m(M_ψ v) ≤ P(ψ_g + tψ) - P` together with the unique equilibrium
of the expansive basic set gives `Re m(M_ψ v) = ∫ ψ dη`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelProductIdentification"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Finset Filter Real Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelHorizonIdentities
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelAnalytic
  PhysicalModelNativeCoefficients PhysicalModelNativeRadiusUpper KellerLiverani1999
  HyperbolicBasicSet ThermodynamicDefinitions FractionalManifoldRegularity

variable {E U M AtlasIndex Reg A Ω Test : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (ν : Measure M) [IsFiniteMeasure ν]
  (aT : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (testView : Test → M →ᵇ ℂ)
  (core : ∀ c t, aT (coreLift m.qa c) t =
    ∫ x, SmoothSupportedManifoldCore.functions V c x * testView t x ∂ν)
  (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
  (one : Test) (hone : ∀ x, testView one x = 1)
  (ψ : M → ℝ) (hψ : ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ) (CR CA : ℝ)
  (regularBound : ∀ c, ‖m.regularCore (coreMultiplier ψ hψ c)‖ ≤ CR * ‖m.regularCore c‖)
  (analyticBound : ∀ c, ‖coreLift m.qa (coreMultiplier ψ hψ c)‖ ≤ CA * ‖coreLift m.qa c‖)

/-- The tilted potential is the potential plus `tψ` on the basic set. -/
theorem tilted_potential_eqOn {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V)
    (g : M → ℝ) (positive : ∀ x ∈ Λ, 0 < g x) (t : ℝ) :
    EqOn (bd.hyperbolic.potential (fun x => g x * exp (t * ψ x)))
      (fun x => bd.hyperbolic.potential g x + t * ψ x) Λ := fun x hx => by
  simp only [HyperbolicData.potential]
  rw [log_mul (positive x hx).ne' (exp_pos _).ne', log_exp]
  ring

set_option maxHeartbeats 40000000 in
include core hphys hone regularBound analyticBound in
/-- The spectral product functional is the integral against the unique equilibrium state. -/
theorem product_identification {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (seed : Reg)
    (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) (mapCont : Continuous (m.maps a))
    (weightCont : Continuous m.weight) (weightNonneg : ∀ x, 0 ≤ m.weight x)
    (d : DeterministicLeading (m.generator a)) (P0 : ℝ) (hrate : d.rate = exp P0)
    {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V) (hT : (T : M → M) = m.maps a)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm) (mixing : MixingOn T Λ)
    (weightRegular : Regular (E := E) (F := ℝ) q m.weight)
    (weightPos : ∀ x ∈ Λ, 0 < m.weight x)
    (weightSupport : Function.support m.weight ⊆ closure V)
    (hP0 : pressure T (bd.hyperbolic.potential m.weight) Λ = (P0 : EReal))
    (refData : FiniteSmoothReferenceCharts.Data (E := E) (M := M)) (νE : Measure E)
    [νE.IsAddHaarMeasure] (hν : ν = refData.measure νE)
    (η : ProbabilityMeasure M) (hη : IsEquilibriumState T (bd.hyperbolic.potential m.weight) Λ η)
    (unique : ∀ μ, IsEquilibriumState T (bd.hyperbolic.potential m.weight) Λ μ → μ = η) :
    (d.mean (strongMultiplier m ψ hψ d.vector)).re = ∫ x, ψ x ∂(η : Measure M) := by
  obtain ⟨c, cpos, expansive⟩ := bd.exists_expansivity_radius forward inverse
  exact identification_of_tangent_family T Λ bd.hyperbolic.compact bd.nonempty
    bd.hyperbolic.invariant c cpos expansive bd.hyperbolic.potential m.weight ψ hψ.continuous
    (bd.hyperbolic.continuousOn_potential forward (inverse.mdifferentiable one_ne_zero) m.weight
      weightCont.continuousOn weightPos)
    (fun t => tilted_potential_eqOn ψ bd m.weight weightPos t) P0 hP0 η hη unique _
    (fun t => product_tangent m ν aT testView core physReg hphys one hone ψ hψ CR CA
      regularBound analyticBound bound a seed hseed mapCont weightCont weightNonneg d P0 hrate bd hT
      forward inverse regularity weightOrder forwardRegular inverseRegular mixing weightRegular
      weightPos weightSupport hP0 refData νE hν t)

end ConditionedStochasticStabilityHyperbolic.PhysicalModelHorizonIdentities
