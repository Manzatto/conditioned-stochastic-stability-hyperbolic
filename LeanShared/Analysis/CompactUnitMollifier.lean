module
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic

/-! A normalized real smooth mollifier in the unit ball, constructed
from Mathlib's genuine bump function for the given Haar measure. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace LeanShared.CompactUnitMollifier
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_kernel_radius (μ:Measure E) [μ.IsAddHaarMeasure] (ρ:ℝ) (hp:0<ρ):
    ∃κ:E→ℝ,ContDiff ℝ 1 κ ∧HasCompactSupport κ ∧
      Function.support κ⊆Metric.closedBall 0 ρ ∧(∫y,κ y ∂μ)=1:=by
  let f:ContDiffBump (0:E):=⟨ρ/2,ρ,by linarith,by linarith⟩
  refine ⟨f.normed μ,?_,f.hasCompactSupport_normed,?_,f.integral_normed⟩
  · exact f.contDiff_normed (n:=1)
  · rw [f.support_normed_eq]
    exact Metric.ball_subset_closedBall

theorem exists_kernel (μ:Measure E) [μ.IsAddHaarMeasure]:
    ∃κ:E→ℝ,ContDiff ℝ 1 κ ∧HasCompactSupport κ ∧
      Function.support κ⊆Metric.closedBall 0 1 ∧(∫y,κ y ∂μ)=1:=
  exists_kernel_radius μ 1 zero_lt_one
end LeanShared.CompactUnitMollifier
