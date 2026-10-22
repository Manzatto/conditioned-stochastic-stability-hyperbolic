module

public import LeanShared.Dynamics.EmpiricalProbability
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Krylov–Bogolyubov existence using actual finite orbit averages. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.EmpiricalProbability
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The failure of invariance of an orbit average tends to zero, tested
against every bounded continuous real function. -/
theorem integral_coboundary_tendsto (T : X → X) (x : X) (f : X →ᵇ ℝ) :
    Tendsto (fun n => (∫ y, f (T y) ∂measure T x n) -
      (∫ y, f y ∂measure T x n)) atTop (𝓝 0) := by
  simp_rw [integral_coboundary]
  have bounded (n : ℕ) :
      ‖(n+1 : ℝ)⁻¹ * (f (T^[n+1] x) - f x)‖ ≤ (n+1 : ℝ)⁻¹ * (2*‖f‖) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    exact mul_le_mul_of_nonneg_left
      (calc ‖f (T^[n+1] x) - f x‖ ≤ ‖f (T^[n+1] x)‖ + ‖f x‖ := norm_sub_le _ _
            _ ≤ 2*‖f‖ := by linarith [f.norm_coe_le_norm (T^[n+1] x), f.norm_coe_le_norm x])
      (inv_nonneg.mpr (by positivity))
  apply squeeze_zero_norm bounded
  simpa only [one_div, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2*‖f‖)

/-- Any weak subsequential limit of orbit averages is invariant. -/
theorem invariant_of_orbit_limit (T : X → X) (continuous : Continuous T) (x : X)
    (ν : ProbabilityMeasure X) (φ : ℕ → ℕ) (mono : StrictMono φ)
    (convergence : Tendsto (fun n => probabilityMeasure T x (φ n)) atTop (𝓝 ν)) :
    MeasurePreserving T (ν : Measure X) (ν : Measure X) := by
  refine ⟨continuous.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable continuous.measurable f.continuous.stronglyMeasurable]
  have first := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp convergence)
    (f.compContinuous ⟨T, continuous⟩)
  have second := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp convergence) f
  have difference := (integral_coboundary_tendsto T x f).comp mono.tendsto_atTop
  have equal : (∫ y, f (T y) ∂(ν : Measure X)) - (∫ y, f y ∂(ν : Measure X)) = 0 :=
    tendsto_nhds_unique (first.sub second) difference
  exact sub_eq_zero.mp equal

/-- Every continuous self-map of a nonempty compact metric space admits
an invariant Borel probability measure. No invariant measure is assumed. -/
theorem exists_invariant_probability [CompactSpace X] [Nonempty X]
    (T : X → X) (continuous : Continuous T) :
    ∃ ν : ProbabilityMeasure X, MeasurePreserving T (ν : Measure X) (ν : Measure X) := by
  let x : X := Classical.arbitrary X
  obtain ⟨ν, _, φ, mono, convergence⟩ :=
    isSeqCompact_univ (fun n => mem_univ (probabilityMeasure T x n))
  exact ⟨ν, invariant_of_orbit_limit T continuous x ν φ mono convergence⟩

end LeanShared.EmpiricalProbability
