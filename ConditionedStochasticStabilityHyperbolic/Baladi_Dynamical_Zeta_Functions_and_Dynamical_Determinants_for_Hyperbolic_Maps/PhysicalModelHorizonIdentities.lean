module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeRadiusUpper
public import ConditionedStochasticStabilityHyperbolic.Spectral.ConstructedRegularMultipliers
public import LeanShared.Geometry.SupportedCoreMultipliers
meta import Lean.LibrarySuggestions.Basic

/-! Literal horizon identities of a physical model. With a faithful test distribution, a
constant-one test and the regular seed of the weight, the paired generator iterates of the
realized seed are the weighted orbit masses `∫ g_{n+1}`, and inserting the strong multiplier by
a smooth real function `ψ` after `n - j` steps gives `∫ g_{n+1} · ψ ∘ T^j`. The strong and
regular multipliers are the completed literal core multiplications. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelHorizonIdentities"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Finset
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelHorizonIdentities
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelAnalytic
  PhysicalModelNativeCoefficients PhysicalModelNativeRadiusUpper

variable {E U M AtlasIndex Reg A Ω Test : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
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

/-- The weighted orbit product splits along an intermediate time. -/
theorem product_split (F : M → M) (g : M → ℝ) (x : M) (j k : ℕ) :
    (∏ i ∈ range j, g (F^[i] x)) * ∏ i ∈ range k, g (F^[i] (F^[j] x)) =
      ∏ i ∈ range (j + k), g (F^[i] x) := by
  rw [prod_range_add]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [← Function.iterate_add_apply, add_comm]

set_option maxHeartbeats 1600000 in
include core hphys hone in
/-- The paired iterates of the realized seed are the weighted orbit masses. -/
theorem orbit_mass {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (seed : Reg)
    (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) (n : ℕ) :
    aT ((m.generator a)^[n] (m.realize seed)) one =
      ((∫ x, ∏ j ∈ range (n + 1), m.weight ((m.maps a)^[j] x) ∂ν : ℝ) : ℂ) := by
  rw [iterate_coefficient m ν aT testView core physReg hphys bound a seed one n,
    ← integral_complex_ofReal]
  congr 1
  funext x
  rw [hone, hseed, prod_range_succ]
  push_cast
  ring

section Multiplier
variable (ψ : M → ℝ) (hψ : ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ)

/-- The literal multiplication of the supported core by `ψ`. -/
abbrev coreMultiplier : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
    SmoothSupportedManifoldCore.core (E := E) V :=
  SmoothSupportedManifoldCore.multiplier V (fun x => (ψ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hψ)

/-- The regular-core realization of the model. -/
abbrev realization : RegularCoreApproximation.Realization (Reg := Reg) (A := m.StrongSpace)
    (Core := SmoothSupportedManifoldCore.core (E := E) V) (X := M) :=
  ⟨m.regularCore, m.regularCore_dense, m.realize, physReg⟩

/-- The strong multiplier by `ψ`. -/
abbrev strongMultiplier : m.StrongSpace →L[ℂ] m.StrongSpace :=
  ConstructedRegularMultipliers.analyticMultiplier (coreLift m.qa) (coreMultiplier ψ hψ)

/-- The regular multiplier by `ψ`. -/
abbrev regularMultiplier : Reg →L[ℂ] Reg :=
  ConstructedRegularMultipliers.regularMultiplier m.regularCore (coreMultiplier ψ hψ)

variable (CR CA : ℝ)
  (regularBound : ∀ c, ‖m.regularCore (coreMultiplier ψ hψ c)‖ ≤ CR * ‖m.regularCore c‖)
  (analyticBound : ∀ c, ‖coreLift m.qa (coreMultiplier ψ hψ c)‖ ≤ CA * ‖coreLift m.qa c‖)

include physReg regularBound analyticBound in
theorem strong_realize (r : Reg) :
    strongMultiplier m ψ hψ (m.realize r) = m.realize (regularMultiplier m ψ hψ r) :=
  (DFunLike.congr_fun (ConstructedRegularMultipliers.analytic_multiplier_law
    (D := realization m physReg) (q := m.regularCore) (hqcore := fun _ => rfl)
    (qa := coreLift m.qa) (hqa := coreLift_dense m.qa)
    (haCore := fun c => m.realize_core c) (multiply := coreMultiplier ψ hψ)
    (CR := CR) (CA := CA) (hregularBound := regularBound) (hanalyticBound := analyticBound))
    r).symm

include hphys regularBound in
theorem view_regularMultiplier (r : Reg) (x : M) :
    m.view (regularMultiplier m ψ hψ r) x = m.view r x * (ψ x : ℂ) := by
  have law := ConstructedRegularMultipliers.physical_multiplier_law
    (D := realization m physReg) (q := m.regularCore) (hqcore := fun _ => rfl)
    (multiply := coreMultiplier ψ hψ)
    (h := BoundedContinuousFunction.mkOfCompact ⟨ψ, hψ.continuous⟩)
    (hphysicalCore := fun c => by
      ext x
      change physReg (m.regularCore (coreMultiplier ψ hψ c)) x =
        physReg (m.regularCore c) x * (ψ x : ℂ)
      rw [hphys, hphys, m.view_core, m.view_core]
      rfl)
    (CR := CR) (hregularBound := regularBound) r
  have := congrArg (fun f : M →ᵇ ℂ => f x) law
  simpa only [hphys, BoundedContinuousFunction.mul_apply,
    AbsorbingMarkovChains.ComplexKernel.ofReal_apply, BoundedContinuousFunction.mkOfCompact_apply,
    ContinuousMap.coe_mk] using this

set_option maxHeartbeats 3200000 in
include core hphys hone regularBound analyticBound in
/-- Inserting the strong multiplier after `n - j` steps gives the weighted Birkhoff term. -/
theorem horizon_term {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (seed : Reg)
    (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) (n j : ℕ) (hj : j ≤ n) :
    aT ((m.generator a)^[j] (strongMultiplier m ψ hψ ((m.generator a)^[n - j] (m.realize seed))))
      one = ((∫ x, (∏ i ∈ range (n + 1), m.weight ((m.maps a)^[i] x)) * ψ ((m.maps a)^[j] x) ∂ν
        : ℝ) : ℂ) := by
  rw [iterate_intertwining m bound a (n - j) seed,
    strong_realize m physReg ψ hψ CR CA regularBound analyticBound,
    iterate_intertwining m bound a j, realize_coefficient m ν aT testView core physReg hphys,
    ← integral_complex_ofReal]
  congr 1
  funext x
  rw [hone, one_mul, view_iterate_general m a, view_regularMultiplier m physReg hphys ψ hψ CR
    regularBound, view_iterate m a seed hseed]
  have split := product_split (m.maps a) m.weight x j (n - j + 1)
  rw [show j + (n - j + 1) = n + 1 by omega] at split
  rw [← split]
  push_cast
  ring

end Multiplier

end ConditionedStochasticStabilityHyperbolic.PhysicalModelHorizonIdentities
