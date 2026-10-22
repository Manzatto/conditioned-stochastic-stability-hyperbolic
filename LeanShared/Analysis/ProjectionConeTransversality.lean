module
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-! Exact fixed projection cones and quantitative transversality to nearby
actual subspaces. No operator growth or word-length factor is introduced. -/
public noncomputable section
namespace LeanShared.ProjectionConeTransversality
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def cone (P : E →L[ℝ] E) (κ : ℝ) : Set E :=
  {v | ‖P v‖ ≤ κ*‖v-P v‖}

theorem outside_bound (P : E →L[ℝ] E) (κ : ℝ) (positive : 0 < κ)
    (v : E) (outside : v ∉ interior (cone P κ)) :
    ‖v‖ ≤ (1+κ⁻¹)*‖P v‖ := by
  have notStrict : ¬ ‖P v‖ < κ*‖v-P v‖ := by
    intro strict
    apply outside
    have openStrict : IsOpen {w : E | ‖P w‖ < κ*‖w-P w‖} :=
      isOpen_lt (continuous_norm.comp P.continuous)
        ((continuous_norm.comp (continuous_id.sub P.continuous)).const_mul κ)
    have subset : {w : E | ‖P w‖ < κ*‖w-P w‖} ⊆ cone P κ := by
      intro w hw
      change ‖P w‖ ≤ κ*‖w-P w‖
      exact hw.le
    apply interior_mono subset
    rw [openStrict.interior_eq]
    exact strict
  have residual : ‖v-P v‖ ≤ κ⁻¹*‖P v‖ := by
    have fact := (le_div_iff₀ positive).mpr (by simpa only [mul_comm] using (not_lt.mp notStrict))
    simpa only [div_eq_mul_inv, mul_comm] using fact
  calc
    _ ≤ ‖P v‖+‖v-P v‖ := by
      simpa only [add_sub_cancel] using norm_add_le (P v) (v-P v)
    _ ≤ ‖P v‖+κ⁻¹*‖P v‖ := add_le_add le_rfl residual
    _ = _ := by ring

/-- The same fixed cone controls the genuine nearby projection, after a
strict uniform angle margin. -/
theorem nearby_bound (P R : E →L[ℝ] E) (κ δ : ℝ) (positive : 0 < κ)
    (close : ‖P-R‖ ≤ δ) (small : (1+κ⁻¹)*δ < 1)
    (v : E) (outside : v ∉ interior (cone P κ)) :
    ‖v‖ ≤ ((1+κ⁻¹)/(1-(1+κ⁻¹)*δ))*‖R v‖ := by
  have Cpos : 0 < 1+κ⁻¹ := by positivity
  have error : ‖P v‖ ≤ ‖R v‖+δ*‖v‖ := by
    calc
      _ ≤ ‖R v‖+‖(P-R) v‖ := by
        simpa only [sub_apply, add_sub_cancel] using norm_add_le (R v) ((P-R) v)
      _ ≤ _ := add_le_add le_rfl (((P-R).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right close (norm_nonneg v)))
  have initial := (outside_bound P κ positive v outside).trans
    (mul_le_mul_of_nonneg_left error Cpos.le)
  have denominator : 0 < 1-(1+κ⁻¹)*δ := sub_pos.mpr small
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ denominator).mpr
  nlinarith
end LeanShared.ProjectionConeTransversality
