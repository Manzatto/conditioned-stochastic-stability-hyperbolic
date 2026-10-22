module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeRadiusUpper
public import LeanShared.Dynamics.BasicHyperbolicOrbitIntegralGrowth
public import LeanShared.Geometry.FiniteSmoothReferenceMeasure

/-! Upper bound of the spectral radius at the pressure on an arbitrary basic set. The orbit-integral
growth at the pressure, a faithful test distribution with literal core values and a compact
two-norm estimate with principal rate `α ≤ e^P` give `spectralRadius ≤ e^P`. No mixing, positive
eigenvector or leading record is used. -/

public noncomputable section
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

/-- Upper radius bound at the pressure on a basic set, without mixing. -/
theorem radius_upper_at_pressure
    {L : ℝ} (bound : AnalyticBound m L) (a : Ω)
    {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V)
    (hT : (T : M → M) = m.maps a)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (weightCont : Continuous m.weight) (nonnegative : ∀ x, 0 ≤ m.weight x)
    (positive : ∀ x ∈ Λ, 0 < m.weight x) (supported : Function.support m.weight ⊆ closure V)
    (reference : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (νE : Measure E) [νE.IsAddHaarMeasure]
    (P : ℝ) (pressureP : pressure T (bd.hyperbolic.potential m.weight) Λ = (P : EReal))
    {Test : Type*} [NormedAddCommGroup Test] [NormedSpace ℂ Test]
    (aT : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (testView : Test → M →ᵇ ℂ)
    (core : ∀ c t, aT (coreLift m.qa c) t =
      ∫ x, SmoothSupportedManifoldCore.functions V c x * testView t x ∂(reference.measure νE))
    (faithful : Function.Injective aT)
    (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
    {Weak : Type*} [NormedAddCommGroup Weak] [NormedSpace ℂ Weak]
    (weak : m.StrongSpace →L[ℂ] Weak) (compact : IsCompactOperator weak)
    (α B C D : ℝ) (hα : 0 ≤ α) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (estimate : ∀ n v, ‖((m.generator a) ^ n) v‖ ≤ C * α ^ n * ‖v‖ + D * B ^ n * ‖weak v‖)
    (rate : α ≤ Real.exp P) :
    spectralRadius ℂ (m.generator a) ≤ ENNReal.ofReal (Real.exp P) := by
  have upper : ∀ R' : ℝ, Real.exp P < R' → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal (∏ j ∈ Finset.range n, m.weight ((m.maps a)^[j] x))
        ∂(reference.measure νE)) ≤ ENNReal.ofReal (C' * R' ^ n) := by
    intro R' above
    rw [← hT]
    exact bd.orbit_integral_growth_at_pressure forward inverse m.weight weightCont positive
      nonnegative supported reference νE P pressureP R' above
  exact spectralRadius_le m (reference.measure νE) aT testView core physReg hphys bound a faithful
    weak compact α B C D hα hB hC hD estimate nonnegative (Real.exp P) (Real.exp_pos P) rate upper

end ConditionedStochasticStabilityHyperbolic.PhysicalModelNativeRadiusUpper
