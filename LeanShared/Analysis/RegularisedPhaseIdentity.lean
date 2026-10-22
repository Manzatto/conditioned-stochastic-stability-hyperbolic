module
public import LeanShared.Analysis.NonstationaryPhaseIntegration
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-! The exact regularised nonlinear integration-by-parts splitting.
The rough coefficient is only continuous; all differentiation falls on
its actual compact smooth approximant. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace LeanShared.RegularisedPhaseIdentity
open NonstationaryPhaseIntegration
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_oscillation (Λ:ℝ) (φ:E→ℝ) (x:E) : ‖oscillation Λ φ x‖=1 := by
  have eqn:(Λ:ℂ)*Complex.I*(φ x:ℂ)=((Λ*φ x:ℝ):ℂ)*Complex.I:=by push_cast;ring
  rw [oscillation,eqn,Complex.norm_exp_ofReal_mul_I]

omit [FiniteDimensional ℝ E] in
theorem integrable_directed (μ:Measure E) [μ.IsAddHaarMeasure]
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) {h:E→ℂ} (hc:Continuous h) (hs:HasCompactSupport h)
    (Λ:ℝ) (v:E) :
    Integrable (fun x=>oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*h x) μ := by
  have cd:Continuous (fun x=>fderiv ℝ φ x v):=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact (((smooth_oscillation hφ Λ).continuous.mul (Complex.continuous_ofReal.comp cd)).mul hc).integrable_of_hasCompactSupport hs.mul_left

theorem identity (μ:Measure E) [μ.IsAddHaarMeasure]
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) {h:E→ℂ} (hc:Continuous h) (hs:HasCompactSupport h)
    {κ:E→ℂ} (hκ:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ)
    (Λ:ℝ) (hΛ:Λ≠0) (v:E) :
    -Complex.I*(∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*h x ∂μ)=
      (Λ:ℂ)⁻¹*(∫ x,oscillation Λ φ x*fderiv ℝ κ x v ∂μ)+
      -Complex.I*(∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*(h x-κ x) ∂μ) := by
  have difference:(∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*(h x-κ x) ∂μ)=
      (∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*h x ∂μ)-
      (∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*κ x ∂μ):=by
    simp_rw [mul_sub]
    exact integral_sub (integrable_directed μ hφ hc hs Λ v)
      (integrable_directed μ hφ hκ.continuous compact Λ v)
  rw [difference,integration_by_parts μ hφ hκ compact Λ v]
  have nonzero:(Λ:ℂ)≠0:=by exact_mod_cast hΛ
  field_simp [nonzero]
  ring

theorem norm_bound (μ:Measure E) [μ.IsAddHaarMeasure]
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) {h:E→ℂ} (hc:Continuous h) (hs:HasCompactSupport h)
    {κ:E→ℂ} (hκ:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ)
    (Λ:ℝ) (hΛ:Λ≠0) (v:E) :
    ‖∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*h x ∂μ‖≤
      |Λ|⁻¹*(∫ x,‖fderiv ℝ κ x v‖ ∂μ)+
      ∫ x,‖fderiv ℝ φ x v‖*‖h x-κ x‖ ∂μ := by
  have first:‖∫ x,oscillation Λ φ x*fderiv ℝ κ x v ∂μ‖≤∫ x,‖fderiv ℝ κ x v‖ ∂μ:=by
    apply (norm_integral_le_integral_norm _).trans_eq
    simp only [norm_mul,norm_oscillation,one_mul]
  have second:‖∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*(h x-κ x) ∂μ‖≤
      ∫ x,‖fderiv ℝ φ x v‖*‖h x-κ x‖ ∂μ:=by
    apply (norm_integral_le_integral_norm _).trans_eq
    simp only [norm_mul,norm_oscillation,one_mul,Complex.norm_real]
  calc
    _ = ‖-Complex.I*(∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*h x ∂μ)‖:=by
      simp only [norm_mul,norm_neg,Complex.norm_I,one_mul]
    _ = _:=congrArg norm (identity μ hφ hc hs hκ compact Λ hΛ v)
    _ ≤ _:=norm_add_le _ _
    _ = |Λ|⁻¹*‖∫ x,oscillation Λ φ x*fderiv ℝ κ x v ∂μ‖+
        ‖∫ x,oscillation Λ φ x*(fderiv ℝ φ x v:ℂ)*(h x-κ x) ∂μ‖:=by
      simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,norm_neg,Complex.norm_I,one_mul]
    _ ≤ _:=add_le_add (mul_le_mul_of_nonneg_left first (inv_nonneg.mpr (abs_nonneg _))) second
end LeanShared.RegularisedPhaseIdentity
