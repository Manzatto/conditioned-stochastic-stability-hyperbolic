module
public import LeanShared.Analysis.BanachNormalizedKernelDilation
public import LeanShared.Analysis.BanachHolderMollifierDerivative
import Mathlib.Tactic

/-! Actual normalized convolution has the sharp Holder approximation and
one-derivative regularization rates. No smoothing estimate is supplied. -/
public noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Convolution BoundedContinuousFunction
namespace LeanShared.BanachScaledHolderMollification
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ:Measure E) [μ.IsAddHaarMeasure]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
theorem moment_scale (κ:E→ℝ) {r:ℝ} (hr:0<r) (α:ℝ) :
    (∫ x,‖BanachNormalizedKernelDilation.dilate κ r x‖*‖x‖^α ∂μ)=
      (r^α)⁻¹*(∫ x,‖κ x‖*‖x‖^α ∂μ) := by
  have scale(x:E):‖BanachNormalizedKernelDilation.dilate κ r x‖*‖x‖^α=
      (r^Module.finrank ℝ E)*(r^α)⁻¹*(‖κ (r • x)‖*‖r • x‖^α):=by
    simp only [BanachNormalizedKernelDilation.dilate,norm_smul,Real.norm_eq_abs,
      abs_of_pos hr,abs_of_nonneg (pow_nonneg hr.le (Module.finrank ℝ E)),
      Real.mul_rpow hr.le (norm_nonneg x)]
    field_simp
  simp_rw [scale]
  rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg μ
    (fun x:E=>‖κ x‖*‖x‖^α) r (hR:=hr.le),smul_eq_mul]
  have dim:r^Module.finrank ℝ E≠0:=pow_ne_zero _ hr.ne'
  field_simp

theorem error {κ:E→ℝ} (continuous:Continuous κ) (compact:HasCompactSupport κ)
    (mass:∫ x,κ x ∂μ=1) (f:E→ᵇF) {α H:ℝ} (hα:0<α) (_hH:0≤H)
    (holder:∀x y,‖f x-f y‖≤H*‖x-y‖^α) (x:E) :
    ‖(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] f) x-f x‖≤
      H*(∫ y,‖κ y‖*‖y‖^α ∂μ) := by
  have integrable:Integrable κ μ:=continuous.integrable_of_hasCompactSupport compact
  have moment:Integrable (fun y=>‖κ y‖*‖y‖^α) μ:=
    (continuous.norm.mul (continuous_norm.rpow_const (fun _=>Or.inr hα.le))).integrable_of_hasCompactSupport
      ((compact.comp_left (g:=fun z:ℝ=>‖z‖) (by simp)).mul_right)
  have product:Integrable (fun y=>κ y • f (x-y)) μ:=
    integrable.smul_bdd ‖f‖ (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y=>f.norm_coe_le_norm (x-y))
  have subtract:(∫ y,κ y • (f (x-y)-f x) ∂μ)=
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] f) x-f x:=by
    simp_rw [smul_sub]
    rw [integral_sub product (integrable.smul_const (f x)),integral_smul_const,mass,one_smul]
    rfl
  rw [←subtract]
  calc
    _ ≤ ∫ y,‖κ y • (f (x-y)-f x)‖ ∂μ:=norm_integral_le_integral_norm _
    _ ≤ ∫ y,H*(‖κ y‖*‖y‖^α) ∂μ:=
      integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _) (moment.const_mul H)
        (ae_of_all _ fun y=>by
          have bound:‖f (x-y)-f x‖≤H*‖y‖^α:=by
            simpa only [sub_sub_cancel_left,norm_neg] using holder (x-y) x
          change ‖κ y • (f (x-y)-f x)‖≤H*(‖κ y‖*‖y‖^α)
          rw [norm_smul]
          exact (mul_le_mul_of_nonneg_left bound (norm_nonneg _)).trans_eq (by ring))
    _ = _:=integral_const_mul _ _

theorem scaled_error {κ:E→ℝ} (continuous:Continuous κ) (compact:HasCompactSupport κ)
    (mass:∫ x,κ x ∂μ=1) (f:E→ᵇF) {α H:ℝ} (hα:0<α) (hH:0≤H)
    (holder:∀x y,‖f x-f y‖≤H*‖x-y‖^α) {r:ℝ} (hr:0<r) (x:E) :
    ‖(BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] f) x-f x‖≤
      H*(r^α)⁻¹*(∫ y,‖κ y‖*‖y‖^α ∂μ) := by
  have cont:Continuous (BanachNormalizedKernelDilation.dilate κ r):=by
    unfold BanachNormalizedKernelDilation.dilate
    exact (continuous.comp ((continuous_const : Continuous (fun _:E=>r)).smul continuous_id)).const_smul (r^Module.finrank ℝ E)
  have result:=error μ cont (BanachNormalizedKernelDilation.compact compact hr)
    ((BanachNormalizedKernelDilation.integral_dilate μ κ hr).trans mass) f hα hH holder x
  rw [moment_scale μ κ hr α] at result
  exact result.trans_eq (by ring)

theorem scaled_derivative {κ:E→ℝ} (smooth:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ)
    (f:E→ᵇF) {α H:ℝ} (hα:0<α) (hH:0≤H)
    (holder:∀x y,‖f x-f y‖≤H*‖x-y‖^α) {r:ℝ} (hr:0<r) (x:E) :
    ‖fderiv ℝ (BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] f) x‖≤
      H*(r*(r^α)⁻¹)*(∫ y,‖fderiv ℝ κ y‖*‖y‖^α ∂μ) := by
  have result:=BanachHolderMollifierDerivative.derivative_bound μ
    (BanachNormalizedKernelDilation.smooth smooth r) (BanachNormalizedKernelDilation.compact compact hr)
    f hα hH holder x
  rw [BanachNormalizedKernelDilation.derivative_moment μ smooth hr α] at result
  exact result.trans_eq (by ring)
end LeanShared.BanachScaledHolderMollification
