module
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! Genuine nonlinear oscillatory integration by parts. The phase needs
only C¹ regularity when the vectorfield factor is smooth. This is the
identity used with mollified coefficients in regularised integration by
parts, preserving fractional map regularity. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace LeanShared.NonstationaryPhaseIntegration
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def oscillation (Λ:ℝ) (φ:E→ℝ) (x:E) : ℂ:=
  Complex.exp ((Λ:ℂ)*Complex.I*(φ x:ℂ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem smooth_oscillation {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) (Λ:ℝ) :
    ContDiff ℝ 1 (oscillation Λ φ) := by
  let A:ℝ→L[ℝ]ℂ:=((Λ:ℂ)*Complex.I) • Complex.ofRealCLM
  exact (A.contDiff.comp hφ).cexp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem derivative_oscillation {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) (Λ:ℝ) (x v:E) :
    fderiv ℝ (oscillation Λ φ) x v=
      (Λ:ℂ)*Complex.I*(fderiv ℝ φ x v:ℂ)*oscillation Λ φ x := by
  let A:ℝ→L[ℝ]ℂ:=((Λ:ℂ)*Complex.I) • Complex.ofRealCLM
  have derivative:HasFDerivAt (fun y=>Complex.exp (A (φ y)))
      (Complex.exp (A (φ x)) • (A.comp (fderiv ℝ φ x))) x:=
    (A.hasFDerivAt.comp x ((hφ.differentiable (by norm_num) x).hasFDerivAt)).cexp
  change fderiv ℝ (fun y=>Complex.exp (A (φ y))) x v=_
  rw [derivative.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    A,Complex.ofRealCLM_apply,smul_eq_mul]
  change oscillation Λ φ x*((Λ:ℂ)*Complex.I*(fderiv ℝ φ x v:ℂ))=_
  ring

theorem integration_by_parts (μ:Measure E) [μ.IsAddHaarMeasure] {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ)
    {κ:E→ℂ} (hκ:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ) (Λ:ℝ) (v:E) :
    (∫ x,oscillation Λ φ x*fderiv ℝ κ x v ∂μ)=
      -((Λ:ℂ)*Complex.I)*(∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*κ x ∂μ) := by
  have smooth:=smooth_oscillation hφ Λ
  have cderiv:Continuous (fun x=>fderiv ℝ κ x v):=
    (hκ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have compactDeriv:HasCompactSupport (fun x=>fderiv ℝ κ x v):=
    (compact.fderiv ℝ).comp_left (g:=fun L:E→L[ℝ]ℂ=>L v) (by simp)
  have cphase:Continuous (fun x=>fderiv ℝ (oscillation Λ φ) x v):=
    (smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have first:Integrable (fun x=>fderiv ℝ (oscillation Λ φ) x v*κ x) μ:=
    (cphase.mul hκ.continuous).integrable_of_hasCompactSupport compact.mul_left
  have second:Integrable (fun x=>oscillation Λ φ x*fderiv ℝ κ x v) μ:=
    (smooth.continuous.mul cderiv).integrable_of_hasCompactSupport compactDeriv.mul_left
  have product:Integrable (fun x=>oscillation Λ φ x*κ x) μ:=
    (smooth.continuous.mul hκ.continuous).integrable_of_hasCompactSupport compact.mul_left
  have ibp:=integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=μ) (f:=oscillation Λ φ) (g:=κ)
    (v:=v) first second product (fun x _=>smooth.differentiable (by norm_num) x)
    (fun x _=>hκ.differentiable (by norm_num) x)
  calc
    _ = -(∫ x,fderiv ℝ (oscillation Λ φ) x v*κ x ∂μ):=ibp
    _ = -((Λ:ℂ)*Complex.I)*(∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*κ x ∂μ):=by
      simp_rw [derivative_oscillation hφ Λ]
      rw [←integral_neg,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring

/-- The derivative of a genuine compact C¹ kernel has zero integral. -/
theorem integral_derivative_zero (μ:Measure E) [μ.IsAddHaarMeasure]
    {κ:E→ℂ} (hκ:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ) (v:E) :
    (∫ x,fderiv ℝ κ x v ∂μ)=0 := by
  simpa only [oscillation,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,neg_zero]
    using integration_by_parts μ (φ:=fun _:E=>0) contDiff_const hκ compact (0:ℝ) v
end LeanShared.NonstationaryPhaseIntegration

