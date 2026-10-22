module
public import LeanShared.Analysis.ProjectionConeTransversality

/-! Strict one-step cone margins for every actual contraction rate in
`(0,1)`. The inner opening is chosen after the rate, rather than fixed. -/
public noncomputable section
namespace LeanShared.ProjectionConeRateMargin
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def opening (a : ℝ) : ℝ := (1 + a ^ 2) / 2
@[expose] def tolerance (a : ℝ) : ℝ := (1 - a ^ 2) / 16

theorem scalar_bounds {a : ℝ} (positive : 0 < a) (contracting : a < 1) :
    0 < tolerance a ∧ a ^ 2 < opening a ∧ opening a < 1 ∧
      0 < opening a ∧ tolerance a < 1 ∧
      a ^ 2 + 2 * a * tolerance a * (1 + opening a) < opening a := by
  have square : a ^ 2 < 1 := by nlinarith [mul_pos positive (sub_pos.mpr contracting)]
  have positiveTolerance : 0 < tolerance a := by unfold tolerance; linarith
  have inner : a ^ 2 < opening a := by unfold opening; linarith
  have below : opening a < 1 := by unfold opening; linarith
  have positiveOpening : 0 < opening a := by unfold opening; positivity
  have small : tolerance a < 1 := by unfold tolerance; nlinarith [sq_nonneg a]
  have factor : a * (1 + opening a) ≤ 2 := by
    calc
      _ ≤ 1 * (1 + opening a) :=
        mul_le_mul_of_nonneg_right contracting.le (by linarith)
      _ ≤ 2 := by linarith
  have scaled : 2 * a * tolerance a * (1 + opening a) ≤ 4 * tolerance a := by
    have bound := mul_le_mul_of_nonneg_right factor
      (show 0 ≤ 2 * tolerance a by positivity)
    nlinarith
  refine ⟨positiveTolerance, inner, below, positiveOpening, small, ?_⟩
  calc
    _ ≤ a ^ 2 + 4 * tolerance a := by linarith
    _ < opening a := by unfold opening tolerance; linarith

/-- A quantitative component gap gives strict cone action for the actual
nearby operator. The lower estimate is written without division by `a`. -/
theorem strict_action_of_gap (Ps Pu A B : E →L[ℝ] E) (a θ δ : ℝ)
    (positive : 0 < a) (nonnegativeOpening : 0 ≤ θ) (nonnegativeError : 0 ≤ δ)
    (gap : a ^ 2 + 2 * a * δ * (1 + θ) < θ)
    (decompose : ∀ v, Ps v + Pu v = v) (normPs : ‖Ps‖ ≤ 1) (normPu : ‖Pu‖ ≤ 1)
    (lower : ∀ v, ‖Ps v‖ ≤ a * ‖Ps (A v)‖)
    (upper : ∀ v, ‖Pu (A v)‖ ≤ a * ‖Pu v‖)
    (close : ‖B - A‖ ≤ δ) (v : E) (nonzero : v ≠ 0)
    (member : v ∈ ProjectionConeTransversality.cone Pu 1) :
    B v ∈ interior (ProjectionConeTransversality.cone Pu θ) := by
  have complement (w : E) : w - Pu w = Ps w := sub_eq_iff_eq_add.mpr (decompose w).symm
  have input : ‖Pu v‖ ≤ ‖Ps v‖ := by
    simpa only [ProjectionConeTransversality.cone, mem_ofPred_eq, one_mul, complement] using member
  have nv : ‖v‖ ≤ 2 * ‖Ps v‖ := by
    have triangle := norm_add_le (Ps v) (Pu v)
    rw [decompose] at triangle
    linarith
  have positiveComponent : 0 < ‖Ps v‖ := by
    by_contra hn
    have zero : ‖Ps v‖ = 0 := le_antisymm (not_lt.mp hn) (norm_nonneg _)
    have vz : ‖v‖ = 0 := by linarith [norm_nonneg v]
    exact nonzero (norm_eq_zero.mp vz)
  have error : ‖(B - A) v‖ ≤ 2 * δ * ‖Ps v‖ := by
    calc
      _ ≤ δ * ‖v‖ := ((B - A).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right close (norm_nonneg v))
      _ ≤ δ * (2 * ‖Ps v‖) := mul_le_mul_of_nonneg_left nv nonnegativeError
      _ = _ := by ring
  have bound (P : E →L[ℝ] E) (normP : ‖P‖ ≤ 1) :
      ‖P (B v) - P (A v)‖ ≤ 2 * δ * ‖Ps v‖ := by
    have estimate := (P.le_opNorm ((B - A) v)).trans
      (mul_le_mul_of_nonneg_right normP (norm_nonneg _))
    simpa only [map_sub, sub_apply, one_mul] using estimate.trans (by simpa only [one_mul] using error)
  have expansion : ‖Ps v‖ ≤ a * (‖Ps (B v)‖ + 2 * δ * ‖Ps v‖) := by
    have reverse := norm_sub_norm_le (Ps (A v)) (Ps (B v))
    rw [norm_sub_rev] at reverse
    have difference := bound Ps normPs
    exact (lower v).trans (mul_le_mul_of_nonneg_left (by linarith) positive.le)
  have contraction : ‖Pu (B v)‖ ≤ a * ‖Ps v‖ + 2 * δ * ‖Ps v‖ := by
    have reverse := norm_sub_norm_le (Pu (B v)) (Pu (A v))
    have difference := bound Pu normPu
    have actual := (upper v).trans (mul_le_mul_of_nonneg_left input positive.le)
    linarith
  have strict : ‖Pu (B v)‖ < θ * ‖Ps (B v)‖ := by
    have first := mul_le_mul_of_nonneg_left contraction positive.le
    have second := mul_le_mul_of_nonneg_left expansion nonnegativeOpening
    have strictGap := mul_lt_mul_of_pos_right gap positiveComponent
    nlinarith
  have openStrict : IsOpen {w : E | ‖Pu w‖ < θ * ‖Ps w‖} :=
    isOpen_lt Pu.continuous.norm (Ps.continuous.norm.const_mul θ)
  apply interior_mono (show {w : E | ‖Pu w‖ < θ * ‖Ps w‖} ⊆
    ProjectionConeTransversality.cone Pu θ from ?_)
  · rw [openStrict.interior_eq]
    exact strict
  · intro w hw
    simpa only [ProjectionConeTransversality.cone, mem_ofPred_eq, complement] using hw.le

theorem strict_action (Ps Pu A B : E →L[ℝ] E) (a : ℝ)
    (positive : 0 < a) (contracting : a < 1)
    (decompose : ∀ v, Ps v + Pu v = v) (normPs : ‖Ps‖ ≤ 1) (normPu : ‖Pu‖ ≤ 1)
    (lower : ∀ v, ‖Ps v‖ ≤ a * ‖Ps (A v)‖)
    (upper : ∀ v, ‖Pu (A v)‖ ≤ a * ‖Pu v‖)
    (close : ‖B - A‖ ≤ tolerance a) (v : E) (nonzero : v ≠ 0)
    (member : v ∈ ProjectionConeTransversality.cone Pu 1) :
    B v ∈ interior (ProjectionConeTransversality.cone Pu (opening a)) := by
  obtain ⟨posδ, _, _, posθ, _, gap⟩ := scalar_bounds positive contracting
  exact strict_action_of_gap Ps Pu A B a (opening a) (tolerance a) positive posθ.le posδ.le
    gap decompose normPs normPu lower upper close v nonzero member

end LeanShared.ProjectionConeRateMargin
