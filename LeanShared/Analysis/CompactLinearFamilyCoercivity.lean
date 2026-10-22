module
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Uniform upper and lower native bounds for a genuine compact family
of injective finite-dimensional operators. -/
public noncomputable section
open Set
namespace LeanShared.CompactLinearFamilyCoercivity
variable {E X:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] [CompactSpace X]

theorem bounds (A:X→E→L[ℝ] E) (continuous:Continuous A)
    (injective:∀x,Function.Injective (A x)):
    ∃B K:ℝ,1≤B ∧1≤K ∧(∀x,‖A x‖≤B) ∧∀x v,‖v‖≤K*‖A x v‖:=by
  have compactRange:IsCompact (range A):=by simpa only [image_univ] using isCompact_univ.image continuous
  obtain ⟨B,hB,boundB⟩:=compactRange.isBounded.exists_pos_norm_le
  let S:Set (X × E):=univ ×ˢ Metric.sphere 0 1
  have compactS:IsCompact S:=isCompact_univ.prod (isCompact_sphere (0:E) 1)
  have cf:Continuous (fun p:X × E=>‖A p.1 p.2‖):=by fun_prop
  have positive:∀p∈S,0<‖A p.1 p.2‖:=by
    intro p hp
    apply norm_pos_iff.mpr
    intro zero
    have hz:p.2=0:=injective p.1 (by simpa only [map_zero] using zero)
    have norm:‖p.2‖=1:=by simpa only [Metric.mem_sphere,dist_zero_right] using hp.2
    simp only [hz,norm_zero] at norm
    norm_num at norm
  obtain ⟨c,hc,boundC⟩:=compactS.exists_forall_le' cf.continuousOn positive
  have coercive:∀x v,c*‖v‖≤‖A x v‖:=by
    intro x v
    by_cases zero:v=0
    · simp only [zero,map_zero,norm_zero,mul_zero,le_refl]
    have positive:0<‖v‖:=norm_pos_iff.mpr zero
    have h:=boundC (x,‖v‖⁻¹ • v) ⟨mem_univ _,by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr positive.le),inv_mul_cancel₀ positive.ne']⟩
    simp only [map_smul,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr positive.le)] at h
    simpa only [mul_comm] using (le_inv_mul_iff₀ positive).mp h
  refine ⟨max 1 B,max 1 c⁻¹,le_max_left _ _,le_max_left _ _,?_,?_⟩
  · intro x
    exact (boundB (A x) (mem_range_self x)).trans (le_max_right _ _)
  · intro x v
    have h:‖v‖≤c⁻¹*‖A x v‖:=(le_inv_mul_iff₀ hc).2 (coercive x v)
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
end LeanShared.CompactLinearFamilyCoercivity
