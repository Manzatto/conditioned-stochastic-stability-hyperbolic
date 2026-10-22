module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Strict cone action produces quantitative angular separation on the
actual compact annuli, uniformly over a compact derivative family.
The normalized dyadic ratios are allowed to tend to zero. -/
public noncomputable section
open Set
namespace LeanShared.AngularCrossPhaseGap
variable {E X:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] [CompactSpace X]

theorem exists_gap (C D:Set E) (A:X → E→L[ℝ] E) (continuous:Continuous A)
    (injective:∀x,Function.Injective (A x))
    (sourceScale:∀ r : ℝ,0<r → ∀ v, v∉ interior C → r • v∉ interior C)
    (targetScale:∀ r : ℝ,0<r → ∀ v, v∉ interior D → r • v∉ interior D)
    (action:∀x v,v≠0 → v∉ interior C → A x v∈interior D):
    ∃c:ℝ,0<c ∧∀x ξ η r s,ξ∉ interior D → η∉ interior C → 
      1/4≤‖ξ‖ → ‖ξ‖≤4 → 1/4≤‖η‖ → ‖η‖≤4 → 
      r∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → max r s=1 → 
      c≤‖r • ξ-A x (s • η)‖:=by
  let U:Set E:={ξ|ξ∉ interior D ∧1/4≤‖ξ‖}∩Metric.closedBall 0 4
  let V:Set E:={η|η∉ interior C ∧1/4≤‖η‖}∩Metric.closedBall 0 4
  have compactU:IsCompact U:=(isCompact_closedBall (0:E) 4).inter_left
    (isOpen_interior.isClosed_compl.inter (isClosed_le continuous_const continuous_norm))
  have compactV:IsCompact V:=(isCompact_closedBall (0:E) 4).inter_left
    (isOpen_interior.isClosed_compl.inter (isClosed_le continuous_const continuous_norm))
  let R:Set (ℝ × ℝ):=(Icc 0 1 ×ˢ Icc 0 1)∩{p|max p.1 p.2=1}
  have compactR:IsCompact R:=(isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_eq (continuous_fst.max continuous_snd) continuous_const)
  let P:Set (X × ((E × E) × (ℝ × ℝ))):=univ ×ˢ ((U ×ˢ V) ×ˢ R)
  have compactP:IsCompact P:=isCompact_univ.prod ((compactU.prod compactV).prod compactR)
  let f:X × ((E × E) × (ℝ × ℝ)) → ℝ:=fun p=>
    ‖p.2.2.1 • p.2.1.1-A p.1 (p.2.2.2 • p.2.1.2)‖
  have cf:Continuous f:=by
    dsimp only [f]
    fun_prop
  have positive:∀p∈P,0<f p:=by
    intro p hp
    rcases hp with ⟨_,⟨⟨⟨⟨hout,ξlo⟩,ξhi⟩,⟨⟨hin,ηlo⟩,ηhi⟩⟩,⟨⟨hr,hs⟩,hmax⟩⟩⟩
    change max p.2.2.1 p.2.2.2=1 at hmax
    have ξne:p.2.1.1≠0:=by intro h; simp only [h,norm_zero] at ξlo;norm_num at ξlo
    have ηne:p.2.1.2≠0:=by intro h; simp only [h,norm_zero] at ηlo;norm_num at ηlo
    apply norm_pos_iff.mpr
    intro zero
    have eq:p.2.2.1 • p.2.1.1=A p.1 (p.2.2.2 • p.2.1.2):=sub_eq_zero.mp zero
    have rne:p.2.2.1≠0:=by
      intro h
      have az:A p.1 (p.2.2.2 • p.2.1.2)=A p.1 0:=by simpa only [h,zero_smul,map_zero] using eq.symm
      have sz:p.2.2.2=0:=(smul_eq_zero.mp (injective p.1 az)).resolve_right ηne
      simp only [h,sz,max_self] at hmax
      norm_num at hmax
    have sne:p.2.2.2≠0:=by
      intro h
      have rz:p.2.2.1=0:=(smul_eq_zero.mp
        (by simpa only [h,zero_smul,map_zero] using eq)).resolve_right ξne
      simp only [h,rz,max_self] at hmax
      norm_num at hmax
    have rp:0<p.2.2.1:=lt_of_le_of_ne hr.1 rne.symm
    have sp:0<p.2.2.2:=lt_of_le_of_ne hs.1 sne.symm
    have outside:=targetScale _ rp _ hout
    have inside:=action p.1 (p.2.2.2 • p.2.1.2) (smul_ne_zero sne ηne)
      (sourceScale _ sp _ hin)
    exact outside (eq ▸ inside)
  obtain ⟨c,hc,bound⟩:=compactP.exists_forall_le' cf.continuousOn positive
  refine ⟨c,hc,?_⟩
  intro x ξ η r s hout hin ξlo ξhi ηlo ηhi hr hs hm
  exact bound (x,((ξ,η),(r,s))) ⟨mem_univ _,⟨⟨⟨⟨hout,ξlo⟩,
    by simpa only [Metric.mem_closedBall,dist_zero_right] using ξhi⟩,⟨⟨hin,ηlo⟩,
    by simpa only [Metric.mem_closedBall,dist_zero_right] using ηhi⟩⟩,⟨⟨hr,hs⟩,hm⟩⟩⟩
end LeanShared.AngularCrossPhaseGap
