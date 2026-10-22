module
public import LeanShared.Analysis.AmbientLeafFamily

/-! A uniform literal integral bound gives the actual completed ambient
leaf-family norm bound, using its represented L1 coordinates. -/
public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LeanShared.GraphLeafNorm
variable {A U E : Type*} [NormedAddCommGroup U] [NormedAddCommGroup E]
  [MeasurableSpace U] [MeasurableSpace E] {J : ℝ}

theorem ambient_norm_le_of_lintegral (μ : Measure U) (leaves : A → GraphLeaf U E J)
    (z : AmbientFamilySpace μ leaves) (f : E → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (represents : ∀ a,z a =ᵐ[(leaves a).measure μ] f)
    (bound : ∀ a,(∫⁻ x,‖f x‖ₑ ∂(leaves a).measure μ) ≤ ENNReal.ofReal R) :
    ‖z‖ ≤ R := by
  apply lp.norm_le_of_forall_le hR
  intro a
  rw [L1.norm_eq_integral_norm]
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  rw [ofReal_integral_norm_eq_lintegral_enorm (L1.integrable_coeFn (z a))]
  exact (lintegral_congr_ae ((represents a).fun_comp (fun v : ℂ => ‖v‖ₑ))).le.trans (bound a)

end LeanShared.GraphLeafNorm
