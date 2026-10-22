module
public import LeanShared.Analysis.ProjectionConeRateMargin

/-! The original rate-dependent error budget also preserves the literal
half cone strictly. This uses the half-cone input ratio, without replacing
the contraction rate by that of an iterate. -/
public noncomputable section
namespace LeanShared.ProjectionConeHalfMargin
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The original outer-to-half cone estimate is retained verbatim. -/
theorem strict_half_action (Ps Pu A B : E→L[ℝ]E)
    (decompose : ∀v,Ps v+Pu v=v)
    (normPs : ‖Ps‖≤1) (normPu : ‖Pu‖≤1)
    (lower : ∀v,4*‖Ps v‖≤‖Ps (A v)‖)
    (upper : ∀v,‖Pu (A v)‖≤(1/4:ℝ)*‖Pu v‖)
    (close : ‖B-A‖≤1/4) (v : E) (nonzero : v≠0)
    (member : v∈ProjectionConeTransversality.cone Pu 1) :
    B v∈interior (ProjectionConeTransversality.cone Pu (1/2)) := by
  have complement (w : E) : w-Pu w=Ps w := sub_eq_iff_eq_add.mpr (decompose w).symm
  have input : ‖Pu v‖≤‖Ps v‖ := by
    simpa only [ProjectionConeTransversality.cone,mem_ofPred_eq,one_mul,complement] using member
  have nv : ‖v‖≤2*‖Ps v‖ := by
    have triangle := norm_add_le (Ps v) (Pu v)
    rw [decompose] at triangle
    linarith
  have positive : 0<‖Ps v‖ := by
    by_contra hn
    have zero : ‖Ps v‖=0 := le_antisymm (not_lt.mp hn) (norm_nonneg _)
    have vz : ‖v‖=0 := by linarith [norm_nonneg v]
    exact nonzero (norm_eq_zero.mp vz)
  have error := ((B-A).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right close (norm_nonneg v))
  have ep := Ps.le_opNorm ((B-A) v)
  have eu := Pu.le_opNorm ((B-A) v)
  have boundP : ‖Ps (B v)-Ps (A v)‖≤(1/4:ℝ)*‖v‖ := by
    simpa only [map_sub,sub_apply,one_mul] using
      (ep.trans (mul_le_mul_of_nonneg_right normPs (norm_nonneg _))).trans (by simpa only [one_mul] using error)
  have boundU : ‖Pu (B v)-Pu (A v)‖≤(1/4:ℝ)*‖v‖ := by
    simpa only [map_sub,sub_apply,one_mul] using
      (eu.trans (mul_le_mul_of_nonneg_right normPu (norm_nonneg _))).trans (by simpa only [one_mul] using error)
  have strict : ‖Pu (B v)‖<(1/2:ℝ)*‖Ps (B v)‖ := by
    have first := norm_sub_norm_le (Ps (A v)) (Ps (B v))
    rw [norm_sub_rev] at first
    have second := norm_sub_norm_le (Pu (B v)) (Pu (A v))
    have l := lower v
    have u := upper v
    nlinarith
  have openStrict : IsOpen {w : E | ‖Pu w‖<(1/2:ℝ)*‖Ps w‖} :=
    isOpen_lt Pu.continuous.norm (Ps.continuous.norm.const_mul (1/2))
  apply interior_mono (show {w : E | ‖Pu w‖<(1/2:ℝ)*‖Ps w‖}⊆ProjectionConeTransversality.cone Pu (1/2) from ?_)
  · rw [openStrict.interior_eq]
    exact strict
  · intro w hw
    simpa only [ProjectionConeTransversality.cone,mem_ofPred_eq,one_mul,complement] using hw.le

theorem strict_action (Ps Pu A B : E →L[ℝ] E) (a : ℝ)
    (positive : 0 < a) (contracting : a < 1)
    (decompose : ∀ v, Ps v + Pu v = v) (normPs : ‖Ps‖ ≤ 1) (normPu : ‖Pu‖ ≤ 1)
    (lower : ∀ v, ‖Ps v‖ ≤ a * ‖Ps (A v)‖)
    (upper : ∀ v, ‖Pu (A v)‖ ≤ a * ‖Pu v‖)
    (close : ‖B - A‖ ≤ ProjectionConeRateMargin.tolerance a)
    (v : E) (nonzero : v ≠ 0)
    (member : v ∈ ProjectionConeTransversality.cone Pu (1/2)) :
    B v ∈ interior (ProjectionConeTransversality.cone Pu (1/2)) := by
  let δ := ProjectionConeRateMargin.tolerance a
  have positiveδ : 0 < δ := (ProjectionConeRateMargin.scalar_bounds positive contracting).1
  have gap : a ^ 2 + 6 * a * δ < 1 := by
    have square : a ^ 2 < 1 := by nlinarith
    have scaled := mul_le_mul_of_nonneg_right contracting.le positiveδ.le
    dsimp only [δ, ProjectionConeRateMargin.tolerance] at *
    nlinarith
  have complement (w : E) : w - Pu w = Ps w := sub_eq_iff_eq_add.mpr (decompose w).symm
  have input : ‖Pu v‖ ≤ (1/2:ℝ) * ‖Ps v‖ := by
    simpa only [ProjectionConeTransversality.cone, mem_ofPred_eq, complement] using member
  have nv : ‖v‖ ≤ 2 * ‖Ps v‖ := by
    have triangle := norm_add_le (Ps v) (Pu v)
    rw [decompose] at triangle
    linarith [norm_nonneg (Ps v)]
  have positiveComponent : 0 < ‖Ps v‖ := by
    by_contra hn
    have vz : ‖v‖ = 0 := by linarith [norm_nonneg v, norm_nonneg (Ps v)]
    exact nonzero (norm_eq_zero.mp vz)
  have error : ‖(B - A) v‖ ≤ 2 * δ * ‖Ps v‖ := by
    calc
      _ ≤ δ * ‖v‖ := ((B - A).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right close (norm_nonneg v))
      _ ≤ δ * (2 * ‖Ps v‖) := mul_le_mul_of_nonneg_left nv positiveδ.le
      _ = _ := by ring
  have bound (P : E →L[ℝ] E) (normP : ‖P‖ ≤ 1) :
      ‖P (B v) - P (A v)‖ ≤ 2 * δ * ‖Ps v‖ := by
    have estimate := (P.le_opNorm ((B - A) v)).trans
      (mul_le_mul_of_nonneg_right normP (norm_nonneg _))
    simpa only [map_sub, sub_apply, one_mul] using estimate.trans
      (by simpa only [one_mul] using error)
  have expansion : ‖Ps v‖ ≤ a * (‖Ps (B v)‖ + 2 * δ * ‖Ps v‖) := by
    have reverse := norm_sub_norm_le (Ps (A v)) (Ps (B v))
    rw [norm_sub_rev] at reverse
    have difference := bound Ps normPs
    exact (lower v).trans (mul_le_mul_of_nonneg_left (by linarith) positive.le)
  have contraction : ‖Pu (B v)‖ ≤ (a/2) * ‖Ps v‖ + 2 * δ * ‖Ps v‖ := by
    have reverse := norm_sub_norm_le (Pu (B v)) (Pu (A v))
    have difference := bound Pu normPu
    have actual := (upper v).trans (mul_le_mul_of_nonneg_left input positive.le)
    linarith
  have strict : ‖Pu (B v)‖ < (1/2:ℝ) * ‖Ps (B v)‖ := by
    have first := mul_le_mul_of_nonneg_left contraction positive.le
    have strictGap := mul_lt_mul_of_pos_right gap positiveComponent
    nlinarith
  have openStrict : IsOpen {w : E | ‖Pu w‖ < (1/2:ℝ) * ‖Ps w‖} :=
    isOpen_lt Pu.continuous.norm (Ps.continuous.norm.const_mul (1/2))
  apply interior_mono (show {w : E | ‖Pu w‖ < (1/2:ℝ) * ‖Ps w‖} ⊆
    ProjectionConeTransversality.cone Pu (1/2) from ?_)
  · rw [openStrict.interior_eq]
    exact strict
  · intro w hw
    simpa only [ProjectionConeTransversality.cone, mem_ofPred_eq, complement] using hw.le

end LeanShared.ProjectionConeHalfMargin
