module
public import LeanShared.Analysis.HomogeneousConeInterior
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Same-sign nonlinked separation from the actual cone-restricted
expansion factors. Compactness turns the strict algebraic exclusion
of zero phase into a uniform quantitative gap. -/
public noncomputable section
open Set
namespace LeanShared.RestrictedConePhaseGap
variable {E X:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] [CompactSpace X]

private theorem compact_gap (O I:Set E) (closedO:IsClosed O) (closedI:IsClosed I)
    (Q:Set (ℝ × ℝ)) (closedQ:IsClosed Q)
    (A:X→E→L[ℝ] E) (continuous:Continuous A)
    (nonzero:∀x ξ η r s,ξ∈O → η∈I →
      1/2≤‖ξ‖ → ‖ξ‖≤2 → 1/4≤‖η‖ → ‖η‖≤4 →
      r∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → max r s=1 → (r,s)∈Q →
      r • ξ-A x (s • η)≠0):
    ∃c:ℝ,0<c ∧∀x ξ η r s,ξ∈O → η∈I →
      1/2≤‖ξ‖ → ‖ξ‖≤2 → 1/4≤‖η‖ → ‖η‖≤4 →
      r∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → max r s=1 → (r,s)∈Q →
      c≤‖r • ξ-A x (s • η)‖:=by
  let U:Set E:=(O∩{ξ|1/2≤‖ξ‖})∩Metric.closedBall 0 2
  let V:Set E:=(I∩{η|1/4≤‖η‖})∩Metric.closedBall 0 4
  have compactU:IsCompact U:=(isCompact_closedBall (0:E) 2).inter_left
    (closedO.inter (isClosed_le continuous_const continuous_norm))
  have compactV:IsCompact V:=(isCompact_closedBall (0:E) 4).inter_left
    (closedI.inter (isClosed_le continuous_const continuous_norm))
  let R:Set (ℝ × ℝ):=((Icc 0 1 ×ˢ Icc 0 1)∩{p|max p.1 p.2=1})∩Q
  have compactR:IsCompact R:=((isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_eq (continuous_fst.max continuous_snd) continuous_const)).inter_right closedQ
  let P:Set (X × ((E × E) × (ℝ × ℝ))):=univ ×ˢ ((U ×ˢ V) ×ˢ R)
  have compactP:IsCompact P:=isCompact_univ.prod ((compactU.prod compactV).prod compactR)
  let f:X × ((E × E) × (ℝ × ℝ))→ℝ:=fun p=>
    ‖p.2.2.1 • p.2.1.1-A p.1 (p.2.2.2 • p.2.1.2)‖
  have cf:Continuous f:=by dsimp only [f];fun_prop
  have positive:∀p∈P,0<f p:=by
    intro p hp
    rcases hp with ⟨_,⟨⟨⟨⟨hout,ξlo⟩,ξhi⟩,⟨⟨hin,ηlo⟩,ηhi⟩⟩,⟨⟨⟨hr,hs⟩,hm⟩,hq⟩⟩⟩
    exact norm_pos_iff.mpr (nonzero p.1 _ _ _ _ hout hin ξlo
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using ξhi) ηlo
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using ηhi) hr hs hm hq)
  obtain ⟨c,hc,bound⟩:=compactP.exists_forall_le' cf.continuousOn positive
  refine ⟨c,hc,?_⟩
  intro x ξ η r s hout hin ξlo ξhi ηlo ηhi hr hs hm hq
  exact bound (x,((ξ,η),(r,s))) ⟨mem_univ _,⟨⟨⟨⟨hout,ξlo⟩,
    by simpa only [Metric.mem_closedBall,dist_zero_right] using ξhi⟩,⟨⟨hin,ηlo⟩,
    by simpa only [Metric.mem_closedBall,dist_zero_right] using ηhi⟩⟩,⟨⟨⟨hr,hs⟩,hm⟩,hq⟩⟩⟩

theorem upper_gap {D:Set E} (scale:∀r:ℝ,0≤r → ∀v∈D,r • v∈D)
    (A:X→E→L[ℝ] E) (continuous:Continuous A) {L:ℝ} (positive:0<L)
    (expansion:∀x v,A x v∉interior D → ‖A x v‖≤L*‖v‖):
    ∃c:ℝ,0<c ∧∀x ξ η r s,ξ∉interior D →
      1/2≤‖ξ‖ → ‖ξ‖≤2 → 1/4≤‖η‖ → ‖η‖≤4 →
      r∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → max r s=1 → 16*L*s≤r →
      c≤‖r • ξ-A x (s • η)‖:=by
  obtain ⟨c,hc,bound⟩:=compact_gap (interior D)ᶜ univ isOpen_interior.isClosed_compl isClosed_univ
    {p:ℝ × ℝ|16*L*p.2≤p.1} (isClosed_le (by fun_prop) continuous_fst) A continuous (by
      intro x ξ η r s hout _ ξlo _ _ ηhi hr hs hm hq
      change 16*L*s≤r at hq
      intro zero
      have eq:r • ξ=A x (s • η):=sub_eq_zero.mp zero
      have rp:0<r:=by
        by_contra! no
        have rz:r=0:=le_antisymm no hr.1
        have sz:s=0:=by nlinarith [hs.1]
        simp only [rz,sz,max_self] at hm
        norm_num at hm
      have outside:=HomogeneousConeInterior.outside_scale scale rp hout
      have estimate:=expansion x (s • η) (by simpa only [←eq] using outside)
      rw [←eq] at estimate
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.1,abs_of_nonneg hs.1] at estimate
      nlinarith [mul_le_mul_of_nonneg_left ξlo hr.1,
        mul_le_mul_of_nonneg_left ηhi (mul_nonneg positive.le hs.1)])
  refine ⟨c,hc,?_⟩
  intro x ξ η r s hout ξlo ξhi ηlo ηhi hr hs hm hq
  exact bound x ξ η r s hout (mem_univ _) ξlo ξhi ηlo ηhi hr hs hm hq

theorem lower_gap {C:Set E} (scale:∀r:ℝ,0≤r → ∀v∈C,r • v∈C)
    (A:X→E→L[ℝ] E) (continuous:Continuous A) {K:ℝ} (positive:0<K)
    (expansion:∀x v,v∉interior C → ‖v‖≤K*‖A x v‖):
    ∃c:ℝ,0<c ∧∀x ξ η r s,η∉interior C →
      1/2≤‖ξ‖ → ‖ξ‖≤2 → 1/4≤‖η‖ → ‖η‖≤4 →
      r∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 → max r s=1 → 16*K*r≤s →
      c≤‖r • ξ-A x (s • η)‖:=by
  obtain ⟨c,hc,bound⟩:=compact_gap univ (interior C)ᶜ isClosed_univ isOpen_interior.isClosed_compl
    {p:ℝ × ℝ|16*K*p.1≤p.2} (isClosed_le (by fun_prop) continuous_snd) A continuous (by
      intro x ξ η r s _ hin ξlo ξhi ηlo _ hr hs hm hq
      change 16*K*r≤s at hq
      intro zero
      have eq:r • ξ=A x (s • η):=sub_eq_zero.mp zero
      have sp:0<s:=by
        by_contra! no
        have sz:s=0:=le_antisymm no hs.1
        have rz:r=0:=by nlinarith [hr.1]
        simp only [rz,sz,max_self] at hm
        norm_num at hm
      have outside:=HomogeneousConeInterior.outside_scale scale sp hin
      have estimate:=expansion x (s • η) outside
      rw [←eq] at estimate
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.1,abs_of_nonneg hs.1] at estimate
      nlinarith [mul_le_mul_of_nonneg_left ηlo hs.1,
        mul_le_mul_of_nonneg_left ξhi (mul_nonneg positive.le hr.1)])
  refine ⟨c,hc,?_⟩
  intro x ξ η r s hin ξlo ξhi ηlo ηhi hr hs hm hq
  exact bound x ξ η r s (mem_univ _) hin ξlo ξhi ηlo ηhi hr hs hm hq
end LeanShared.RestrictedConePhaseGap
