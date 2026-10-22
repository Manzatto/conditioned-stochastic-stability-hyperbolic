module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalytic
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalCarrierPressureFromCoefficients
public import LeanShared.Analysis.InvariantFiniteRegularCompatibility
meta import Lean.LibrarySuggestions.Basic

/-! Native mass coefficients and the pressure lower bound of the generator radius. Under the
one-step analytic bound the completed generator intertwines the finite-regular action; its
powers on a regular seed representing the weight are the weighted orbit products; a strong
pairing that restricts on regular inputs to the integral of the view therefore has coefficients
equal to the literal weighted orbit integrals, and the geometric growth gives `exp P ≤` the
generator radius. No row source or specialized regular carrier is used. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelNativeCoefficients"

public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeCoefficients
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelAnalytic

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

/-- The finite-regular action of a letter. -/
abbrev regularOperator (a : Ω) : Reg →L[ℂ] Reg :=
  InvariantFiniteRegularTransfer.operator m.view m.view_injective m.maps m.weight m.invariant
    m.regularConstant m.regularBound a

/-- The completed generator intertwines the finite-regular action. -/
theorem regular_intertwining {L : ℝ} (bound : AnalyticBound m L) (a : Ω) :
    m.realize.comp (regularOperator m a) = (m.generator a).comp m.realize :=
  InvariantFiniteRegularCompatibility.analytic_intertwining m.qa
    (SmoothSupportedManifoldCore.functions V) m.regularCore m.regularCore_dense
    m.view m.view_injective m.view_core m.realize m.realize_core m.maps m.weight
    m.invariant m.coreRegular m.regularConstant m.regularBound L bound a

theorem iterate_intertwining {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (n : ℕ) (r : Reg) :
    (m.generator a)^[n] (m.realize r) = m.realize ((regularOperator m a)^[n] r) := by
  have semi : Function.Semiconj m.realize (regularOperator m a) (m.generator a) := fun r =>
    DFunLike.congr_fun (regular_intertwining m bound a) r
  exact (semi.iterate_right n r).symm

theorem view_iterate (a : Ω) (seed : Reg) (hseed : ∀ x, m.view seed x = (m.weight x : ℂ))
    (n : ℕ) (x : M) :
    m.view ((regularOperator m a)^[n] seed) x =
      ((∏ j ∈ Finset.range (n + 1), m.weight ((m.maps a)^[j] x) : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero =>
    rw [Function.iterate_zero_apply, hseed, Finset.prod_range_one, Function.iterate_zero_apply]
  | succ n ih =>
    rw [Function.iterate_succ_apply', InvariantFiniteRegularTransfer.operator_function, ih,
      Finset.prod_range_succ' _ (n + 1)]
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    push_cast
    ring

set_option maxHeartbeats 1600000 in
/-- The pairing coefficients are the literal weighted orbit integrals. -/
theorem coefficient {L : ℝ} (bound : AnalyticBound m L) (ν : Measure M)
    (pairing : m.StrongSpace →L[ℂ] ℂ) (integral : Reg →L[ℂ] ℂ)
    (hpair : ∀ r, pairing (m.realize r) = integral r) (hint : ∀ r, integral r = ∫ x, m.view r x ∂ν)
    (integrableView : ∀ r, Integrable (m.view r) ν)
    (a : Ω) (F : M → M) (hF : m.maps a = F)
    (seed : Reg) (hseed : ∀ x, m.view seed x = (m.weight x : ℂ))
    (nonnegative : ∀ x, 0 ≤ m.weight x) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (∏ j ∈ Finset.range (n + 1), m.weight (F^[j] x)) ∂ν) =
      ENNReal.ofReal ‖pairing ((m.generator a)^[n] (m.realize seed))‖ := by
  subst hF
  have nonnegProduct (x : M) : 0 ≤ ∏ j ∈ Finset.range (n + 1), m.weight ((m.maps a)^[j] x) :=
    Finset.prod_nonneg fun _ _ => nonnegative _
  have value : pairing ((m.generator a)^[n] (m.realize seed)) =
      ((∫ x, ∏ j ∈ Finset.range (n + 1), m.weight ((m.maps a)^[j] x) ∂ν : ℝ) : ℂ) := by
    rw [iterate_intertwining m bound a n seed, hpair, hint, ← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => view_iterate m a seed hseed n x)
  have integrable : Integrable (fun x => ∏ j ∈ Finset.range (n + 1), m.weight ((m.maps a)^[j] x)) ν := by
    have h := (integrableView ((regularOperator m a)^[n] seed)).re
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    change (m.view ((regularOperator m a)^[n] seed) x).re = _
    rw [view_iterate m a seed hseed n x, Complex.ofReal_re]
  rw [value, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg nonnegProduct)]
  exact (ofReal_integral_eq_lintegral_ofReal integrable (Filter.Eventually.of_forall nonnegProduct)).symm

section Radius
variable [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

set_option maxHeartbeats 1600000 in
/-- The native pressure lower bound of the generator radius. -/
theorem exp_pressure_le_generatorRadius {L : ℝ} (bound : AnalyticBound m L)
    (T : M ≃ₜ M) (Λ : Set M) (b : HyperbolicBasicSet.BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (mixing : HyperbolicBasicSet.MixingOn T Λ)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (νE : Measure E) [νE.IsAddHaarMeasure]
    (weightRegular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q m.weight)
    (positive : ∀ x ∈ Λ, 0 < m.weight x) (nonnegative : ∀ x, 0 ≤ m.weight x)
    (pressureValue : ℝ)
    (pressure_eq : ThermodynamicDefinitions.pressure T (b.hyperbolic.potential m.weight) Λ =
      (pressureValue : EReal))
    (a : Ω) (map_eq : m.maps a = T)
    (pairing : m.StrongSpace →L[ℂ] ℂ) (integral : Reg →L[ℂ] ℂ)
    (hpair : ∀ r, pairing (m.realize r) = integral r)
    (hint : ∀ r, integral r = ∫ x, m.view r x ∂(referenceMeasure.measure νE))
    (integrableView : ∀ r, Integrable (m.view r) (referenceMeasure.measure νE))
    (seed : Reg) (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) :
    ENNReal.ofReal (Real.exp pressureValue) ≤ m.generatorRadius a := by
  apply m.exp_pressure_le_generatorRadius_from_coefficients T Λ b regularity weightOrder
    forwardRegular inverseRegular mixing referenceMeasure νE weightRegular positive pressureValue
    pressure_eq a pairing (m.realize seed)
  intro n
  have h := coefficient m bound (referenceMeasure.measure νE) pairing integral hpair hint
    integrableView a T map_eq seed hseed nonnegative n
  refine h.trans (congrArg (fun z => ENNReal.ofReal ‖pairing z‖)
    (congrFun (FunLike.coe_pow_eq_iterate (m.normedCarrierGenerator a) n) _).symm)

end Radius

end ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeCoefficients
