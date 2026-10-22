module
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Tactic.Linarith

/-! A genuine endpoint projection map with fixed norm and angle constants.
No choice of a moving orthonormal basis or isometry is needed. -/
public noncomputable section
namespace LeanShared.ProjectedEndpointMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

@[expose] def map (U : Submodule ℝ E) (R : E→L[ℝ]E) : E→L[ℝ]U :=
  U.orthogonalProjectionOnto.comp R

theorem bounds (V U : Submodule ℝ E) (R : E→L[ℝ]E)
    (source : ‖V.starProjection-U.starProjection‖≤(1/16:ℝ))
    (target : ‖R-V.starProjection‖≤(1/16:ℝ)) :
    ‖map U R‖≤2 ∧ ∀v:E, ‖V.starProjection v‖≤‖map U R v‖+(1/8:ℝ)*‖v‖ := by
  have targetError (v:E) : ‖R v-V.starProjection v‖≤(1/16:ℝ)*‖v‖ :=
    ((R-V.starProjection).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right target (norm_nonneg v))
  have Rbound (v:E) : ‖R v‖≤2*‖v‖ := by
    have triangle := norm_sub_norm_le (R v) (V.starProjection v)
    have contraction := V.norm_starProjection_apply_le v
    have error := targetError v
    nlinarith [norm_nonneg v]
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v=>
    (U.norm_orthogonalProjectionOnto_apply_le (R v)).trans (Rbound v)),?_⟩
  intro v
  have first : ‖V.starProjection v-U.starProjection (V.starProjection v)‖≤(1/16:ℝ)*‖v‖ := by
    have fixed : V.starProjection (V.starProjection v)=V.starProjection v :=
      V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem v)
    have estimate := ((V.starProjection-U.starProjection).le_opNorm (V.starProjection v)).trans
      (mul_le_mul_of_nonneg_right source (norm_nonneg _))
    change ‖V.starProjection (V.starProjection v)-U.starProjection (V.starProjection v)‖≤_ at estimate
    rw [fixed] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_left (V.norm_starProjection_apply_le v) (by norm_num))
  have second : ‖U.starProjection (V.starProjection v)-U.starProjection (R v)‖≤(1/16:ℝ)*‖v‖ := by
    rw [←map_sub]
    exact (U.norm_starProjection_apply_le _).trans (by simpa only [norm_sub_rev] using targetError v)
  have difference : ‖V.starProjection v-U.starProjection (R v)‖≤(1/8:ℝ)*‖v‖ := by
    have triangle := norm_add_le (V.starProjection v-U.starProjection (V.starProjection v))
      (U.starProjection (V.starProjection v)-U.starProjection (R v))
    rw [sub_add_sub_cancel] at triangle
    exact triangle.trans (by linarith)
  have triangle := norm_sub_norm_le (V.starProjection v) (U.starProjection (R v))
  have normQ : ‖U.starProjection (R v)‖=‖map U R v‖ := rfl
  rw [normQ] at triangle
  linarith
end LeanShared.ProjectedEndpointMap
