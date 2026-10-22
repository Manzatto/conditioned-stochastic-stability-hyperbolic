module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Complex.Basic

/-! The correlation kernel `κ(y) = ∫ ρ(s) ρ'(y + s) ds` of two continuous compactly supported
functions: continuity, support radius, total mass and `L¹` bound. -/
public noncomputable section
open MeasureTheory Set
namespace LeanShared.MollifierKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The correlation kernel. -/
@[expose] def kernel (ρ ρ' : E → ℂ) (y : E) : ℂ := ∫ s, ρ s * ρ' (y + s)

variable (ρ ρ' : E → ℂ) (ρc : Continuous ρ) (ρcs : HasCompactSupport ρ)
  (ρ'c : Continuous ρ') (ρ'cs : HasCompactSupport ρ')

include ρc ρcs ρ'c ρ'cs in
theorem continuous : Continuous (kernel ρ ρ') := by
  obtain ⟨B, hB⟩ := ρ'c.norm.bddAbove_range_of_hasCompactSupport ρ'cs.norm
  refine continuous_of_dominated (bound := fun s => ‖ρ s‖ * B) ?_ ?_
    ((ρc.integrable_of_hasCompactSupport ρcs).norm.mul_const B) ?_
  · exact fun y => (ρc.mul (ρ'c.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · exact fun y => ae_of_all _ fun s => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB ⟨_, rfl⟩) (norm_nonneg _)
  · exact ae_of_all _ fun s => continuous_const.mul (ρ'c.comp (continuous_id.add continuous_const))

theorem zero_outside {r r' : ℝ} (hρ : ∀ s, r < ‖s‖ → ρ s = 0) (hρ' : ∀ s, r' < ‖s‖ → ρ' s = 0)
    (y : E) (hy : r + r' < ‖y‖) : kernel ρ ρ' y = 0 := by
  refine integral_eq_zero_of_ae (ae_of_all _ fun s => ?_)
  by_cases hs : r < ‖s‖
  · simp [hρ s hs]
  · have far : r' < ‖y + s‖ := by
      have := norm_sub_norm_le y (-s)
      rw [norm_neg, sub_neg_eq_add] at this
      linarith [not_lt.mp hs]
    simp [hρ' _ far]

theorem hasCompactSupport {r r' : ℝ} (hρ : ∀ s, r < ‖s‖ → ρ s = 0)
    (hρ' : ∀ s, r' < ‖s‖ → ρ' s = 0) : HasCompactSupport (kernel ρ ρ') :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (r + r')) fun y hy =>
    zero_outside ρ ρ' hρ hρ' y (by rwa [Metric.mem_closedBall, dist_zero_right, not_le] at hy)

include ρc ρcs ρ'c ρ'cs in
theorem product_integrable :
    Integrable (Function.uncurry fun (y s : E) => ρ s * ρ' (y + s)) (volume.prod volume) := by
  have cont : Continuous (Function.uncurry fun (y s : E) => ρ s * ρ' (y + s)) :=
    (ρc.comp continuous_snd).mul (ρ'c.comp (continuous_fst.add continuous_snd))
  refine (integrable_prod_iff' cont.aestronglyMeasurable).mpr ⟨ae_of_all _ fun s => ?_, ?_⟩
  · exact ((ρ'c.integrable_of_hasCompactSupport ρ'cs).comp_add_right s).const_mul (ρ s)
  · have same : (fun s => ∫ y, ‖Function.uncurry (fun (y s : E) => ρ s * ρ' (y + s)) (y, s)‖) =
        fun s => ‖ρ s‖ * ∫ u, ‖ρ' u‖ := by
      funext s
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [integral_const_mul, integral_add_right_eq_self (fun u => ‖ρ' u‖) s]
    rw [same]
    exact (ρc.integrable_of_hasCompactSupport ρcs).norm.mul_const _

include ρc ρcs ρ'c ρ'cs in
theorem integral : ∫ y, kernel ρ ρ' y = (∫ s, ρ s) * ∫ u, ρ' u := by
  unfold kernel
  rw [integral_integral_swap (product_integrable ρ ρ' ρc ρcs ρ'c ρ'cs), ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [integral_const_mul, integral_add_right_eq_self (fun u => ρ' u) s]

include ρc ρcs ρ'c ρ'cs in
theorem norm_integral_le : ∫ y, ‖kernel ρ ρ' y‖ ≤ (∫ s, ‖ρ s‖) * ∫ u, ‖ρ' u‖ := by
  have normProduct := (product_integrable ρ ρ' ρc ρcs ρ'c ρ'cs).norm
  calc ∫ y, ‖kernel ρ ρ' y‖ ≤ ∫ y, ∫ s, ‖ρ s * ρ' (y + s)‖ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          normProduct.integral_prod_left (ae_of_all _ fun y => norm_integral_le_integral_norm _)
    _ = (∫ s, ‖ρ s‖) * ∫ u, ‖ρ' u‖ := by
        rw [integral_integral_swap normProduct, ← integral_mul_const]
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        simp only [norm_mul]
        rw [integral_const_mul, integral_add_right_eq_self (fun u => ‖ρ' u‖) s]

end LeanShared.MollifierKernel
