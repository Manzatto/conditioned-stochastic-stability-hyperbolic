module
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

/-! Exact normalization and weighted derivative moment of a literal
rescaled compact smoothing kernel. This yields the sharp regularised
integration-by-parts derivative rate, without a scaling-bound premise. -/
public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace LeanShared.NormalizedKernelDilation
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def dilate (κ:E→ℂ) (r:ℝ) (x:E) : ℂ:=
  (r^Module.finrank ℝ E) • κ (r • x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem smooth {κ:E→ℂ} (hκ:ContDiff ℝ 1 κ) (r:ℝ) : ContDiff ℝ 1 (dilate κ r) :=
  (hκ.comp (contDiff_const.smul contDiff_id)).const_smul _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compact {κ:E→ℂ} (hκ:HasCompactSupport κ) {r:ℝ} (hr:0<r) :
    HasCompactSupport (dilate κ r) := by
  have c:HasCompactSupport (fun x:E=>κ (r • x)):=
    hκ.comp_homeomorph (Homeomorph.smulOfNeZero r hr.ne')
  exact HasCompactSupport.smul_left (f:=fun _:E=>r^Module.finrank ℝ E) c

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem derivative {κ:E→ℂ} (hκ:ContDiff ℝ 1 κ) (r:ℝ) (x:E) :
    fderiv ℝ (dilate κ r) x=
      (r^Module.finrank ℝ E*r) • fderiv ℝ κ (r • x) := by
  have scaling:HasFDerivAt (fun y:E=>r • y) (r • ContinuousLinearMap.id ℝ E) x:=
    (hasFDerivAt_id x).const_smul r
  have d:=(((hκ.differentiable (by norm_num) (r • x)).hasFDerivAt).comp x scaling).const_smul (r^Module.finrank ℝ E)
  change fderiv ℝ (fun y:E=>(r^Module.finrank ℝ E) • κ (r • y)) x=_
  apply d.fderiv.trans
  ext v
  simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,map_smul,smul_smul]

theorem integral_dilate (μ:Measure E) [μ.IsAddHaarMeasure] (κ:E→ℂ) {r:ℝ} (hr:0<r) :
    (∫ x,dilate κ r x ∂μ)=∫ x,κ x ∂μ := by
  simp only [dilate]
  rw [integral_smul,Measure.integral_comp_smul_of_nonneg μ κ r (hR:=hr.le),smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),one_smul]

theorem derivative_moment (μ:Measure E) [μ.IsAddHaarMeasure]
    {κ:E→ℂ} (hκ:ContDiff ℝ 1 κ) {r:ℝ} (hr:0<r) (α:ℝ) :
    (∫ x,‖fderiv ℝ (dilate κ r) x‖*‖x‖^α ∂μ)=
      (r*(r^α)⁻¹)*(∫ x,‖fderiv ℝ κ x‖*‖x‖^α ∂μ) := by
  have scale(x:E):‖fderiv ℝ (dilate κ r) x‖*‖x‖^α=
      (r^Module.finrank ℝ E*r)*(r^α)⁻¹ *
        (‖fderiv ℝ κ (r • x)‖*‖r • x‖^α):=by
    rw [derivative hκ r x,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),
      norm_smul,Real.norm_eq_abs,abs_of_pos hr,Real.mul_rpow hr.le (norm_nonneg _)]
    field_simp
  simp_rw [scale]
  rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg μ
    (fun x:E=>‖fderiv ℝ κ x‖*‖x‖^α) r (hR:=hr.le),smul_eq_mul]
  have dim:r^Module.finrank ℝ E≠0:=pow_ne_zero _ hr.ne'
  field_simp
end LeanShared.NormalizedKernelDilation
