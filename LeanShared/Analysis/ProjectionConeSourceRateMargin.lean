module
public import LeanShared.Analysis.ProjectionConeRateMargin

/-! Strict cone action from an arbitrary source opening. This generalizes
`ProjectionConeRateMargin.strict_action_of_gap`, whose source cone has
opening one, and also records that the image of a nonzero vector is nonzero. -/
public noncomputable section
namespace LeanShared.ProjectionConeSourceRateMargin
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem strict_action_of_source_gap (Ps Pu A B : E →L[ℝ] E) (a σ θ δ : ℝ)
    (positive : 0 < a) (nonnegativeSource : 0 ≤ σ) (nonnegativeOpening : 0 ≤ θ)
    (nonnegativeError : 0 ≤ δ)
    (gap : a ^ 2 * σ + a * (1 + σ) * δ * (1 + θ) < θ)
    (decompose : ∀ v, Ps v + Pu v = v) (normPs : ‖Ps‖ ≤ 1) (normPu : ‖Pu‖ ≤ 1)
    (lower : ∀ v, ‖Ps v‖ ≤ a * ‖Ps (A v)‖)
    (upper : ∀ v, ‖Pu (A v)‖ ≤ a * ‖Pu v‖)
    (close : ‖B - A‖ ≤ δ) (v : E) (nonzero : v ≠ 0)
    (member : v ∈ ProjectionConeTransversality.cone Pu σ) :
    B v ≠ 0 ∧ B v ∈ interior (ProjectionConeTransversality.cone Pu θ) := by
  have complement (w : E) : w - Pu w = Ps w := sub_eq_iff_eq_add.mpr (decompose w).symm
  have input : ‖Pu v‖ ≤ σ * ‖Ps v‖ := by
    simpa only [ProjectionConeTransversality.cone, mem_ofPred_eq, complement] using member
  have nv : ‖v‖ ≤ (1 + σ) * ‖Ps v‖ := by
    have triangle := norm_add_le (Ps v) (Pu v)
    rw [decompose] at triangle
    linarith
  have positiveComponent : 0 < ‖Ps v‖ := by
    by_contra hn
    have zero : ‖Ps v‖ = 0 := le_antisymm (not_lt.mp hn) (norm_nonneg _)
    have vz : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact nonzero (norm_eq_zero.mp vz)
  have error : ‖(B - A) v‖ ≤ (1 + σ) * δ * ‖Ps v‖ := by
    calc
      _ ≤ δ * ‖v‖ := ((B - A).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right close (norm_nonneg v))
      _ ≤ δ * ((1 + σ) * ‖Ps v‖) := mul_le_mul_of_nonneg_left nv nonnegativeError
      _ = _ := by ring
  have bound (P : E →L[ℝ] E) (normP : ‖P‖ ≤ 1) :
      ‖P (B v) - P (A v)‖ ≤ (1 + σ) * δ * ‖Ps v‖ := by
    have estimate := (P.le_opNorm ((B - A) v)).trans
      (mul_le_mul_of_nonneg_right normP (norm_nonneg _))
    simpa only [map_sub, sub_apply, one_mul] using
      estimate.trans (by simpa only [one_mul] using error)
  have expansion : ‖Ps v‖ ≤ a * (‖Ps (B v)‖ + (1 + σ) * δ * ‖Ps v‖) := by
    have reverse := norm_sub_norm_le (Ps (A v)) (Ps (B v))
    rw [norm_sub_rev] at reverse
    have difference := bound Ps normPs
    exact (lower v).trans (mul_le_mul_of_nonneg_left (by linarith) positive.le)
  have contraction : ‖Pu (B v)‖ ≤ a * σ * ‖Ps v‖ + (1 + σ) * δ * ‖Ps v‖ := by
    have reverse := norm_sub_norm_le (Pu (B v)) (Pu (A v))
    have difference := bound Pu normPu
    have actual := (upper v).trans (mul_le_mul_of_nonneg_left input positive.le)
    nlinarith
  have strict : ‖Pu (B v)‖ < θ * ‖Ps (B v)‖ := by
    have first := mul_le_mul_of_nonneg_left contraction positive.le
    have second := mul_le_mul_of_nonneg_left expansion nonnegativeOpening
    have strictGap := mul_lt_mul_of_pos_right gap positiveComponent
    nlinarith
  refine ⟨?_, ?_⟩
  · intro zero
    rw [zero, map_zero, map_zero, norm_zero, mul_zero] at strict
    exact lt_irrefl 0 strict
  have openStrict : IsOpen {w : E | ‖Pu w‖ < θ * ‖Ps w‖} :=
    isOpen_lt Pu.continuous.norm (Ps.continuous.norm.const_mul θ)
  apply interior_mono (show {w : E | ‖Pu w‖ < θ * ‖Ps w‖} ⊆
    ProjectionConeTransversality.cone Pu θ from ?_)
  · rw [openStrict.interior_eq]
    exact strict
  · intro w hw
    simpa only [ProjectionConeTransversality.cone, mem_ofPred_eq, complement] using hw.le

end LeanShared.ProjectionConeSourceRateMargin
