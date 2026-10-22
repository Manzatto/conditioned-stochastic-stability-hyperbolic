module
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! An actual smooth replacement for the reciprocal denominator in a
nonstationary phase coefficient. It agrees exactly with inversion in
the separated region and vanishes on a neighborhood of zero. -/
public noncomputable section
open scoped ContDiff Topology
namespace LeanShared.SmoothSeparatedReciprocal

@[expose] def bump {δ:ℝ} (positive:0<δ):ContDiffBump (0:ℝ):=
  ⟨δ/2,δ,half_pos positive,half_lt_self positive⟩

@[expose] def function {δ:ℝ} (positive:0<δ) (u:ℝ):ℝ:=
  (1-bump positive u)*u⁻¹

theorem zero_near {δ:ℝ} (positive:0<δ) {u:ℝ} (near:|u|≤δ/2):
    function positive u=0:=by
  have one:= (bump positive).one_of_mem_closedBall (x:=u)
    (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,bump] using near)
  simp only [function,one,sub_self,zero_mul]

theorem reciprocal {δ:ℝ} (positive:0<δ) {u:ℝ} (separated:δ≤u):
    function positive u=u⁻¹:=by
  have zero: bump positive u=0:=(bump positive).zero_of_le_dist (by
    change δ≤dist u 0
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (positive.le.trans separated)]
    exact separated)
  simp only [function,zero,sub_zero,one_mul]

theorem smooth {δ:ℝ} (positive:0<δ):ContDiff ℝ ∞ (function positive):=by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu:u=0
  · subst u
    apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [(bump positive).eventuallyEq_one] with y hy
    simp only [function,hy,sub_self,zero_mul,Pi.one_apply]
  · exact (contDiffAt_const.sub (bump positive).contDiffAt).mul (contDiffAt_id.inv hu)
end LeanShared.SmoothSeparatedReciprocal
