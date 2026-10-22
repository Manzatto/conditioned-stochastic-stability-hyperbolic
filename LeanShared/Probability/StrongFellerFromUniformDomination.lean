module
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Weak Feller kernels uniformly dominated by one regular reference measure
are strong Feller. Continuous observables approximate each reference-integrable
observable in L1; domination makes the approximation uniform in the state. -/
public noncomputable section
namespace LeanShared.StrongFellerFromUniformDomination
open MeasureTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

theorem integral_distance_le
    {Y : Type*} [MeasurableSpace Y] (σ κ : Measure Y) (c : ℝ≥0)
    (bound : κ ≤ (c : ℝ≥0∞) • σ) {f g : Y → ℝ}
    (integrableF : Integrable f σ) (integrableG : Integrable g σ) :
    dist (∫ y, f y ∂κ) (∫ y, g y ∂κ) ≤
      (c : ℝ) * ∫ y, ‖f y - g y‖ ∂σ := by
  have upperF : Integrable f ((c : ℝ≥0∞) • σ) := integrableF.smul_measure_nnreal
  have upperG : Integrable g ((c : ℝ≥0∞) • σ) := integrableG.smul_measure_nnreal
  have actualF := upperF.mono_measure bound
  have actualG := upperG.mono_measure bound
  rw [dist_eq_norm, ← integral_sub actualF actualG]
  calc
    ‖∫ y, (f y - g y) ∂κ‖ ≤ ∫ y, ‖f y - g y‖ ∂κ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖f y - g y‖ ∂((c : ℝ≥0∞) • σ) :=
      integral_mono_measure bound (ae_of_all _ (fun y => norm_nonneg _)) (upperF.sub upperG).norm
    _ = (c : ℝ) * ∫ y, ‖f y - g y‖ ∂σ := by
      rw [integral_smul_measure]
      simp only [ENNReal.coe_toReal, smul_eq_mul]

theorem continuous_integral
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (σ : Measure Y) [σ.WeaklyRegular] (κ : X → Measure Y) (c : ℝ≥0)
    (bound : ∀ x, κ x ≤ (c : ℝ≥0∞) • σ)
    (weakFeller : ∀ g : Y →ᵇ ℝ, Continuous (fun x => ∫ y, g y ∂κ x))
    {f : Y → ℝ} (integrableF : Integrable f σ) :
    Continuous (fun x => ∫ y, f y ∂κ x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε positiveε
  let η := (ε / 4) / ((c : ℝ) + 1)
  have positiveC : 0 < (c : ℝ) + 1 := by positivity
  have positiveη : 0 < η := div_pos (by positivity) positiveC
  obtain ⟨g, error, integrableG⟩ :=
    integrableF.exists_boundedContinuous_integral_sub_le positiveη
  have small : (c : ℝ) * η ≤ ε / 4 := by
    calc
      (c : ℝ) * η ≤ ((c : ℝ) + 1) * η := by gcongr; linarith
      _ = ε / 4 := by dsimp [η]; field_simp
  have uniform (y : X) : dist (∫ z, f z ∂κ y) (∫ z, g z ∂κ y) ≤ ε / 4 :=
    (integral_distance_le σ (κ y) c (bound y) integrableF integrableG).trans
      ((mul_le_mul_of_nonneg_left error c.property).trans small)
  have near := (weakFeller g).continuousAt.eventually
    (Metric.ball_mem_nhds (∫ z, g z ∂κ x) (show 0 < ε / 4 by positivity))
  filter_upwards [near] with y hy
  have middle : dist (∫ z, g z ∂κ y) (∫ z, g z ∂κ x) < ε / 4 := hy
  have last : dist (∫ z, g z ∂κ x) (∫ z, f z ∂κ x) ≤ ε / 4 := by
    rw [dist_comm]
    exact uniform x
  have total := dist_triangle4 (∫ z, f z ∂κ y) (∫ z, g z ∂κ y)
    (∫ z, g z ∂κ x) (∫ z, f z ∂κ x)
  linarith [uniform y]

end LeanShared.StrongFellerFromUniformDomination
