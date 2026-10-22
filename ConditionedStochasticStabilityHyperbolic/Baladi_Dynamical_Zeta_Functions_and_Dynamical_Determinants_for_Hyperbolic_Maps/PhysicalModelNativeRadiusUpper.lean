module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeCoefficients
public import LeanShared.Analysis.PositiveIntegralCoefficientBound
public import LeanShared.Analysis.ScalarCoefficientSpectralExclusion
public import LeanShared.Geometry.SupportedRegularPairing
public import LeanShared.Analysis.ContinuousLinearMapPowApply
meta import Lean.LibrarySuggestions.Basic

/-! The native upper bound of the generator radius. A faithful test-space distribution of the strong
space with literal core values gives, on every realized regular input, the literal reference
integral against the test; the finite-regular powers make every regular/test coefficient of the
generator powers a weighted orbit integral, bounded by the orbit growth. With the compact
two-norm estimates, scalar meromorphic exclusion bounds the spectral radius by every rate above
which the orbit integrals grow. The test space is abstract. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelNativeRadiusUpper"

public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeRadiusUpper
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelAnalytic
  PhysicalModelNativeCoefficients

variable {E U M AtlasIndex Reg A Ω Test : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
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

omit [IsFiniteMeasure ν] in
theorem view_iterate_general (a : Ω) (r : Reg) (n : ℕ) (x : M) :
    m.view ((regularOperator m a)^[n] r) x =
      ((∏ j ∈ Finset.range n, m.weight ((m.maps a)^[j] x) : ℝ) : ℂ) * m.view r ((m.maps a)^[n] x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', InvariantFiniteRegularTransfer.operator_function, ih,
      Finset.prod_range_succ' _ n]
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    push_cast
    ring

set_option maxHeartbeats 1600000 in
include core hphys in
/-- The distribution of a realized regular input is its literal reference integral. -/
theorem realize_coefficient (r : Reg) (t : Test) :
    aT (m.realize r) t = ∫ x, testView t x * m.view r x ∂ν := by
  have dense : DenseRange m.regularCore := m.regularCore_dense
  have left : Continuous (fun r : Reg => aT (m.realize r) t) :=
    ((aT.comp m.realize).continuous).clm_apply continuous_const
  have right : Continuous (fun r : Reg =>
      SupportedRegularPairing.embedding ν physReg (testView t) r) :=
    (SupportedRegularPairing.embedding ν physReg (testView t)).continuous
  have same : (fun r : Reg => aT (m.realize r) t) = fun r : Reg =>
      SupportedRegularPairing.embedding ν physReg (testView t) r := by
    refine dense.equalizer left right (funext fun c => ?_)
    change aT (m.realize (m.regularCore c)) t =
      SupportedRegularPairing.embedding ν physReg (testView t) (m.regularCore c)
    rw [m.realize_core, core, SupportedRegularPairing.embedding_apply]
    congr 1
    funext x
    rw [hphys, m.view_core, mul_comm]
  rw [congrFun same r, SupportedRegularPairing.embedding_apply]
  congr 1
  funext x
  rw [hphys]

set_option maxHeartbeats 1600000 in
include core hphys in
/-- Every regular/test coefficient of the generator iterates is a weighted orbit integral. -/
theorem iterate_coefficient {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (r : Reg) (t : Test)
    (n : ℕ) :
    aT ((m.generator a)^[n] (m.realize r)) t =
      ∫ x, ((∏ j ∈ Finset.range n, m.weight ((m.maps a)^[j] x) : ℝ) : ℂ) *
        m.view r ((m.maps a)^[n] x) * testView t x ∂ν := by
  rw [iterate_intertwining m bound a n r,
    realize_coefficient m ν aT testView core physReg hphys]
  congr 1
  funext x
  rw [view_iterate_general m a r n x]
  ring

set_option maxHeartbeats 1600000 in
include core hphys in
/-- Orbit growth bounds every regular/test coefficient of the generator iterates. -/
theorem coefficient_growth {L : ℝ} (bound : AnalyticBound m L) (a : Ω)
    (nonnegative : ∀ x, 0 ≤ m.weight x) (R' C : ℝ) (hR' : 0 ≤ R') (hC : 0 ≤ C)
    (upper : ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal
      (∏ j ∈ Finset.range n, m.weight ((m.maps a)^[j] x)) ∂ν) ≤ ENNReal.ofReal (C * R' ^ n))
    (r : Reg) (t : Test) :
    ∃ B : ℝ, ∀ n, ‖aT ((m.generator a)^[n] (m.realize r)) t‖ ≤ B * R' ^ n := by
  refine ⟨(‖physReg r‖ * ‖testView t‖) * C, fun n => ?_⟩
  rw [iterate_coefficient m ν aT testView core physReg hphys bound a r t n]
  have h := PositiveIntegralCoefficientBound.norm_integral_le ν
    (fun x => ∏ j ∈ Finset.range n, m.weight ((m.maps a)^[j] x))
    (fun x => Finset.prod_nonneg fun _ _ => nonnegative _)
    (fun x => m.view r ((m.maps a)^[n] x)) (testView t) ‖physReg r‖ ‖testView t‖ (C * R' ^ n)
    (norm_nonneg _) (norm_nonneg _) (mul_nonneg hC (pow_nonneg hR' n))
    (fun x => by rw [← hphys]; exact (physReg r).norm_coe_le_norm _)
    (fun x => (testView t).norm_coe_le_norm x) (upper n)
  calc _ ≤ (‖physReg r‖ * ‖testView t‖) * (C * R' ^ n) := h
    _ = (‖physReg r‖ * ‖testView t‖) * C * R' ^ n := by ring

omit [IsFiniteMeasure ν] in
theorem apply_pow (a : Ω) (n : ℕ) (r : Reg) (t : Test) :
    ((ContinuousLinearMap.apply ℂ ℂ t).comp aT) (((m.generator a) ^ n) (m.realize r)) =
      aT ((m.generator a)^[n] (m.realize r)) t :=
  congrArg (fun z => aT z t) (ContinuousLinearMapPowApply.pow_apply (m.generator a) n _)

set_option maxHeartbeats 1600000 in
include core hphys in
/-- The coefficient growth in the form of the scalar exclusion consumer. -/
theorem test_growth {L : ℝ} (bound : AnalyticBound m L) (a : Ω)
    (nonnegative : ∀ x, 0 ≤ m.weight x) (R : ℝ) (positiveR : 0 < R)
    (upper : ∀ R' : ℝ, R < R' → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal
      (∏ j ∈ Finset.range n, m.weight ((m.maps a)^[j] x)) ∂ν) ≤ ENNReal.ofReal (C * R' ^ n)) :
    ∀ R' : ℝ, R < R' → ∀ (r : Reg) (t : Test), ∃ K : ℝ, ∀ n,
      ‖((ContinuousLinearMap.apply ℂ ℂ t).comp aT) (((m.generator a) ^ n) (m.realize r))‖ ≤
        K * R' ^ n :=
  fun R' above r t =>
    Exists.elim (upper R' above) fun C' hC' =>
      Exists.elim (coefficient_growth m ν aT testView core physReg hphys bound a nonnegative R' C'
          (positiveR.trans above).le hC'.1 hC'.2 r t)
        fun K hK => ⟨K, fun n => (le_of_eq (congrArg norm (apply_pow m aT a n r t))).trans (hK n)⟩

theorem realize_dense : DenseRange m.realize := (coreLift_dense m.qa).mono (by
  rintro _ ⟨c, rfl⟩
  exact ⟨m.regularCore c, m.realize_core c⟩)

theorem separating (faithful : Function.Injective aT) (v : m.StrongSpace)
    (zero : ∀ t : Test, ((ContinuousLinearMap.apply ℂ ℂ t).comp aT) v = 0) : v = 0 :=
  faithful ((ContinuousLinearMap.ext fun t => zero t).trans (map_zero aT).symm)

set_option maxHeartbeats 1600000 in
include core hphys in
/-- The native upper bound of the generator spectral radius. -/
theorem spectralRadius_le {L : ℝ} (bound : AnalyticBound m L) (a : Ω)
    (faithful : Function.Injective aT)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (weak : m.StrongSpace →L[ℂ] W) (compact : IsCompactOperator weak)
    (α B C D : ℝ) (hα : 0 ≤ α) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n v, ‖((m.generator a) ^ n) v‖ ≤ C * α ^ n * ‖v‖ + D * B ^ n * ‖weak v‖)
    (nonnegative : ∀ x, 0 ≤ m.weight x) (R : ℝ) (positiveR : 0 < R) (rate : α ≤ R)
    (upper : ∀ R' : ℝ, R < R' → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal
      (∏ j ∈ Finset.range n, m.weight ((m.maps a)^[j] x)) ∂ν) ≤ ENNReal.ofReal (C * R' ^ n)) :
    spectralRadius ℂ (m.generator a) ≤ ENNReal.ofReal R :=
  ScalarCoefficientSpectralExclusion.spectralRadius_le_of_forall_gt (m.generator a) weak
    compact α B C D hα hB hC hD estimate m.realize (realize_dense m)
    (fun t : Test => (ContinuousLinearMap.apply ℂ ℂ t).comp aT) (separating m aT faithful)
    R positiveR rate
    (test_growth m ν aT testView core physReg hphys bound a nonnegative R positiveR upper)

end ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeRadiusUpper
