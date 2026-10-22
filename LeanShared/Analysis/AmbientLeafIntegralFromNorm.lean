module
public import LeanShared.Analysis.AmbientLeafIntegralBound

/-! The actual ambient leaf supremum norm controls the literal represented
leaf integral, with no separately supplied comparison constant. -/
public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LeanShared.GraphLeafNorm
variable {A U E : Type*} [NormedAddCommGroup U] [NormedAddCommGroup E]
  [MeasurableSpace U] [MeasurableSpace E] {J : ℝ}

theorem ambient_lintegral_le_norm (μ : Measure U) (leaves : A→GraphLeaf U E J)
    (z : AmbientFamilySpace μ leaves) (f : E→ℂ)
    (represents : ∀ a,z a=ᵐ[(leaves a).measure μ] f) (a:A) :
    (∫⁻ x,‖f x‖ₑ ∂(leaves a).measure μ)≤ENNReal.ofReal ‖z‖ := by
  calc
    _ = ∫⁻ x,‖z a x‖ₑ ∂(leaves a).measure μ :=
      lintegral_congr_ae ((represents a).symm.fun_comp (fun v:ℂ=>‖v‖ₑ))
    _ = ENNReal.ofReal ‖z a‖ := by
      rw [L1.norm_eq_integral_norm]
      exact (ofReal_integral_norm_eq_lintegral_enorm (L1.integrable_coeFn (z a))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (lp.norm_apply_le_norm ENNReal.top_ne_zero z a)
end LeanShared.GraphLeafNorm
