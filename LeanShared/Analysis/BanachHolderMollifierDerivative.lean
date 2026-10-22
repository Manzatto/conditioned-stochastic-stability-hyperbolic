module
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Literal real-kernel convolution gains one derivative against a
Holder function with values in any Banach space. The cancellation and
derivative formula are proved, allowing entire finite symbol jets to
be regularized together. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution BoundedContinuousFunction
namespace LeanShared.BanachHolderMollifierDerivative
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem cancellation (μ:Measure E) (k:E→ℝ) (integrable:Integrable k μ)
    (zero:∫y,k y ∂μ=0) (f:E→ᵇF) {a C:ℝ}
    (moment:Integrable (fun y=>‖k y‖*‖y‖^a) μ)
    (holder:∀x y,‖f x-f y‖≤C*‖x-y‖^a) (x:E):
    ‖∫y,k y • f (x-y) ∂μ‖≤C*∫y,‖k y‖*‖y‖^a ∂μ:=by
  have product:Integrable (fun y=>k y • f (x-y)) μ:=integrable.smul_bdd ‖f‖
    (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y=>f.norm_coe_le_norm (x-y))
  have subtract:(∫y,k y • (f (x-y)-f x) ∂μ)=∫y,k y • f (x-y) ∂μ:=by
    simp_rw [smul_sub]
    rw [integral_sub product (integrable.smul_const _),integral_smul_const,zero,zero_smul,sub_zero]
  rw [←subtract]
  calc
    _ ≤ ∫y,‖k y • (f (x-y)-f x)‖ ∂μ:=norm_integral_le_integral_norm _
    _ ≤ ∫y,C*(‖k y‖*‖y‖^a) ∂μ:=integral_mono_of_nonneg
      (ae_of_all _ fun _=>norm_nonneg _) (moment.const_mul C) (ae_of_all _ fun y=>by
        have bound:‖f (x-y)-f x‖≤C*‖y‖^a:=by
          simpa only [sub_sub_cancel_left,norm_neg] using holder (x-y) x
        change ‖k y • (f (x-y)-f x)‖≤C*(‖k y‖*‖y‖^a)
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left bound (norm_nonneg _)).trans_eq (by ring))
    _ = _:=integral_const_mul _ _

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
theorem integral_derivative_zero (μ:Measure E) [μ.IsAddHaarMeasure]
    {κ:E→ℝ} (smooth:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ) (v:E):
    (∫y,fderiv ℝ κ y v ∂μ)=0:=by
  have cont:Continuous (fun y=>fderiv ℝ κ y v):=
    (smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have support:HasCompactSupport (fun y=>fderiv ℝ κ y v):=
    (compact.fderiv ℝ).comp_left (g:=fun L:E→L[ℝ]ℝ=>L v) (by simp)
  have raw:=integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=μ)
    (f:=fun _:E=>(1:ℝ)) (g:=κ) (v:=v)
    (by simp)
    (by simpa using cont.integrable_of_hasCompactSupport support)
    (by simpa using smooth.continuous.integrable_of_hasCompactSupport compact)
    (fun _ _=>differentiableAt_const _) (fun y _=>smooth.differentiable (by norm_num) y)
  simpa using raw

omit [CompleteSpace F] in
theorem derivative_formula (μ:Measure E) [μ.IsAddHaarMeasure]
    {κ:E→ℝ} (smooth:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ)
    (f:E→ᵇF) (x v:E):
    fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>f y)) x v=
      ∫y,fderiv ℝ κ y v • f (x-y) ∂μ:=by
  let L:ℝ→L[ℝ]F→L[ℝ]F:=ContinuousLinearMap.lsmul ℝ ℝ
  have derivative:=compact.hasFDerivAt_convolution_left L smooth
    (f.continuous.locallyIntegrable (μ:=μ)) x
  have integrable:Integrable (fun y=>(L.precompL E) (fderiv ℝ κ y) (f (x-y))) μ:=
    (compact.fderiv ℝ).convolutionExists_left (L.precompL E)
      (smooth.continuous_fderiv (by norm_num)) (f.continuous.locallyIntegrable (μ:=μ)) x
  rw [derivative.fderiv,convolution_def,ContinuousLinearMap.integral_apply integrable]
  rfl

theorem derivative_bound (μ:Measure E) [μ.IsAddHaarMeasure]
    {κ:E→ℝ} (smooth:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ)
    (f:E→ᵇF) {a C:ℝ} (ha:0<a) (hC:0≤C)
    (holder:∀x y,‖f x-f y‖≤C*‖x-y‖^a) (x:E):
    ‖fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>f y)) x‖≤
      C*(∫y,‖fderiv ℝ κ y‖*‖y‖^a ∂μ):=by
  have moment:Integrable (fun y=>‖fderiv ℝ κ y‖*‖y‖^a) μ:=
    ((smooth.continuous_fderiv (by norm_num)).norm.mul
      (continuous_norm.rpow_const (fun _=>Or.inr ha.le))).integrable_of_hasCompactSupport
      (((compact.fderiv ℝ).comp_left (g:=fun L:E→L[ℝ]ℝ=>‖L‖) (by simp)).mul_right)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (integral_nonneg (fun _=>by positivity)))
  intro v
  have cont:Continuous (fun y=>fderiv ℝ κ y v):=
    (smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have support:HasCompactSupport (fun y=>fderiv ℝ κ y v):=
    (compact.fderiv ℝ).comp_left (g:=fun L:E→L[ℝ]ℝ=>L v) (by simp)
  have momentV:Integrable (fun y=>‖fderiv ℝ κ y v‖*‖y‖^a) μ:=
    (cont.norm.mul (continuous_norm.rpow_const (fun _=>Or.inr ha.le))).integrable_of_hasCompactSupport
      ((support.comp_left (g:=fun y:ℝ=>‖y‖) (by simp)).mul_right)
  rw [derivative_formula μ smooth compact f x v]
  have raw:=cancellation μ (fun y=>fderiv ℝ κ y v)
    (cont.integrable_of_hasCompactSupport support) (integral_derivative_zero μ smooth compact v)
    f momentV holder x
  have compare:(∫y,‖fderiv ℝ κ y v‖*‖y‖^a ∂μ)≤
      (∫y,‖fderiv ℝ κ y‖*‖y‖^a ∂μ)*‖v‖:=by
    rw [←integral_mul_const]
    apply integral_mono momentV (moment.mul_const ‖v‖)
    intro y
    exact (mul_le_mul_of_nonneg_right ((fderiv ℝ κ y).le_opNorm v)
      (Real.rpow_nonneg (norm_nonneg _) a)).trans_eq (by ring)
  exact raw.trans ((mul_le_mul_of_nonneg_left compare hC).trans_eq (by ring))
end LeanShared.BanachHolderMollifierDerivative
