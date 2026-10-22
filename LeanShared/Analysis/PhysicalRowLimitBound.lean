module
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! Uniform finite physical row estimates pass to the actual pointwise
limit by Fatou. No equality with a formally summed block operator is assumed. -/
public section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace LeanShared.PhysicalRowLimitBound
variable {X : Type*} [MeasurableSpace X]

theorem bound (μ : Measure X) (f : ℕ → X → ℂ) (g : X → ℂ)
    (measurable : ∀ n, Measurable (f n))
    (converges : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (B : ℝ≥0∞) (finiteBound : ∀ n, ∫⁻ x,‖f n x‖ₑ ∂μ ≤ B) :
    ∫⁻ x,‖g x‖ₑ ∂μ ≤ B := by
  have limit (x : X) : liminf (fun n => ‖f n x‖ₑ) atTop = ‖g x‖ₑ :=
    ((continuous_enorm.tendsto (g x)).comp (converges x)).liminf_eq
  have fatou := lintegral_liminf_le (μ := μ) (u := atTop) (fun n => (measurable n).enorm)
  rw [show (fun x => liminf (fun n => ‖f n x‖ₑ) atTop) = (fun x => ‖g x‖ₑ) from funext limit] at fatou
  have upper := Filter.liminf_le_liminf (f := atTop) (Filter.Eventually.of_forall finiteBound)
  exact fatou.trans (by simpa only [liminf_const] using upper)

end LeanShared.PhysicalRowLimitBound
