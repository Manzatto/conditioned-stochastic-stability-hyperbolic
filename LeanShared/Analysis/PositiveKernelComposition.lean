module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

/-! Tonelli and the actual Bochner integral give the positive row
majorant associated with a physical two-kernel estimate. -/
public noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace LeanShared.PositiveKernelComposition
variable {E:Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem identity (μ ν:Measure E) [SFinite μ] [SFinite ν]
    (G:E→E) (measurableG:Measurable G) (a k₀ k₁ u:E→ℝ≥0∞)
    (ma:Measurable a) (m₀:Measurable k₀) (m₁:Measurable k₁) (mu:Measurable u) (x:E):
    (∫⁻y,(∫⁻w,k₀ (x-w)*a w*k₁ (G w-y) ∂μ)*u y ∂ν)=
      ∫⁻w,k₀ (x-w)*a w*(∫⁻y,k₁ (G w-y)*u y ∂ν) ∂μ:=by
  have joint:Measurable (fun p:E × E=>k₀ (x-p.1)*a p.1*k₁ (G p.1-p.2)*u p.2):=
    (((m₀.comp (measurable_const.sub measurable_fst)).mul (ma.comp measurable_fst)).mul
      (m₁.comp ((measurableG.comp measurable_fst).sub measurable_snd))).mul (mu.comp measurable_snd)
  calc
    _=∫⁻y,(∫⁻w,k₀ (x-w)*a w*k₁ (G w-y)*u y ∂μ) ∂ν:=by
      apply lintegral_congr
      intro y
      exact (lintegral_mul_const (u y) (((m₀.comp (measurable_const.sub measurable_id)).mul ma).mul
        (m₁.comp (measurableG.sub measurable_const)))).symm
    _=∫⁻w,(∫⁻y,k₀ (x-w)*a w*k₁ (G w-y)*u y ∂ν) ∂μ:=
      (lintegral_lintegral_swap joint.aemeasurable).symm
    _=_:=by
      apply lintegral_congr
      intro w
      have innerMeas:Measurable (fun y:E=>k₁ (G w-y)*u y):=
        (m₁.comp ((measurable_const : Measurable (fun _:E=>G w)).sub measurable_id)).mul mu
      calc
        _=∫⁻y,(k₀ (x-w)*a w)*(k₁ (G w-y)*u y) ∂ν:=by
          apply lintegral_congr
          intro y
          ring
        _=_:=lintegral_const_mul _ innerMeas

theorem operator_bound (μ ν:Measure E) [SFinite μ] [SFinite ν]
    (G:E→E) (measurableG:Measurable G) (a k₀ k₁:E→ℝ≥0∞)
    (ma:Measurable a) (m₀:Measurable k₀) (m₁:Measurable k₁)
    (u:E→ℂ) (mu:Measurable u) (K:E→ℂ) (C:ℝ≥0) (x:E)
    (bound:∀y,‖K y‖ₑ≤(C:ℝ≥0∞)*(∫⁻w,k₀ (x-w)*a w*k₁ (G w-y) ∂μ)):
    ‖∫y,K y*u y ∂ν‖ₑ≤(C:ℝ≥0∞)*
      (∫⁻w,k₀ (x-w)*a w*(∫⁻y,k₁ (G w-y)*‖u y‖ₑ ∂ν) ∂μ):=by
  calc
    _≤∫⁻y,‖K y‖ₑ*‖u y‖ₑ ∂ν:=by
      simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (μ:=ν) (fun y=>K y*u y)
    _≤∫⁻y,(C:ℝ≥0∞)*((∫⁻w,k₀ (x-w)*a w*k₁ (G w-y) ∂μ)*‖u y‖ₑ) ∂ν:=by
      apply lintegral_mono
      intro y
      exact (mul_le_mul_of_nonneg_right (bound y) bot_le).trans_eq (by ring)
    _=(C:ℝ≥0∞)*(∫⁻y,(∫⁻w,k₀ (x-w)*a w*k₁ (G w-y) ∂μ)*‖u y‖ₑ ∂ν):=
      lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _=_:=congrArg (fun v:ℝ≥0∞=>(C:ℝ≥0∞)*v)
      (identity μ ν G measurableG a k₀ k₁ (fun y=>‖u y‖ₑ) ma m₀ m₁ mu.enorm x)
end LeanShared.PositiveKernelComposition
