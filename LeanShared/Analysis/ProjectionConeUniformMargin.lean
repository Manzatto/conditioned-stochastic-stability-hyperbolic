module
public import LeanShared.Analysis.ProjectionConeTransversality

/-! A fixed quantitative margin preserves a projection cone. The radius is
independent of the reference operator, provided its stated hyperbolic
component estimates hold. -/
public noncomputable section
namespace LeanShared.ProjectionConeUniformMargin
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem strict_action (Ps Pu A B : E→L[ℝ]E)
    (decompose : ∀v,Ps v+Pu v=v)
    (normPs : ‖Ps‖≤1) (normPu : ‖Pu‖≤1)
    (lower : ∀v,4*‖Ps v‖≤‖Ps (A v)‖)
    (upper : ∀v,‖Pu (A v)‖≤(1/4:ℝ)*‖Pu v‖)
    (close : ‖B-A‖≤1/4) (v : E) (nonzero : v≠0)
    (member : v∈ProjectionConeTransversality.cone Pu 1) :
    B v∈interior (ProjectionConeTransversality.cone Pu 1) := by
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
  have strict : ‖Pu (B v)‖<‖Ps (B v)‖ := by
    have first := norm_sub_norm_le (Ps (A v)) (Ps (B v))
    rw [norm_sub_rev] at first
    have second := norm_sub_norm_le (Pu (B v)) (Pu (A v))
    have l := lower v
    have u := upper v
    nlinarith
  have openStrict : IsOpen {w : E | ‖Pu w‖<‖Ps w‖} :=
    isOpen_lt Pu.continuous.norm Ps.continuous.norm
  apply interior_mono (show {w : E | ‖Pu w‖<‖Ps w‖}⊆ProjectionConeTransversality.cone Pu 1 from ?_)
  · rw [openStrict.interior_eq]
    exact strict
  · intro w hw
    simpa only [ProjectionConeTransversality.cone,mem_ofPred_eq,one_mul,complement] using hw.le

end LeanShared.ProjectionConeUniformMargin
