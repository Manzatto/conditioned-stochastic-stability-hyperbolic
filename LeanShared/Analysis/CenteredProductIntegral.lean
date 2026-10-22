module
public import LeanShared.Analysis.HilbertFrequencyPair
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Integrating the sharp centered envelope retains the physical
convolution geometry instead of replacing it by the volume of support. -/
public noncomputable section
open Set MeasureTheory
namespace LeanShared.CenteredProductIntegral
open HilbertFrequencyPair
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_envelope (m:ℕ):Continuous (envelope (E:=E) m):=by
  unfold envelope
  exact (continuous_const.add continuous_norm |>.pow m).inv₀ (fun x=>pow_ne_zero m (by positivity : (1+‖x‖:ℝ)≠0))

omit [FiniteDimensional ℝ E] in
theorem bound (μ:Measure E) [IsFiniteMeasureOnCompacts μ] {L:Set E} (compactL:IsCompact L)
    (m:ℕ) (G:E→E) (gc:Continuous G) (x y:E) (a b C:ℝ) (f:E→ℂ)
    (estimate:∀w∈L,‖f w‖≤C*envelope m (a • (x-w))*envelope m (b • (G w-y))):
    ‖∫w in L,f w ∂μ‖≤C*(∫w in L,envelope m (a • (x-w))*envelope m (b • (G w-y)) ∂μ):=by
  have c:Continuous (fun w=>envelope m (a • (x-w))*envelope m (b • (G w-y))):=
    ((continuous_envelope m).comp (continuous_const.smul (continuous_const.sub continuous_id))).mul
      ((continuous_envelope m).comp (continuous_const.smul (gc.sub continuous_const)))
  have int:IntegrableOn (fun w=>C*(envelope m (a • (x-w))*envelope m (b • (G w-y)))) L μ:=
    (continuous_const.mul c).continuousOn.integrableOn_compact compactL
  have raw:=norm_integral_le_of_norm_le int (ae_restrict_of_forall_mem compactL.measurableSet
    (fun w hw=>(estimate w hw).trans_eq (mul_assoc _ _ _)))
  exact raw.trans_eq (integral_const_mul C _)
end LeanShared.CenteredProductIntegral
