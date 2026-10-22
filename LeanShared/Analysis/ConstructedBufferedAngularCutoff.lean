module
public import LeanShared.Analysis.CompactSmoothCutoff
public import LeanShared.Analysis.ConeDyadicSymbols

/-! Genuine smooth angular cutoffs with support collars. These collars
also construct the enlarged input multipliers equal to one on the
original angular supports. -/
public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace LeanShared.ConstructedBufferedAngularCutoff
open ConeDyadicSymbols
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Cp Cm:Set E}

theorem exists_cutoff (closedP:IsClosed Cp) (closedM:IsClosed Cm)
    (disjoint:∀ξ∈Cp,‖ξ‖=1 → ξ∉Cm):
    ∃Φ:AngularCutoff Cp Cm,ContDiff ℝ ∞ Φ.toFun ∧ HasCompactSupport Φ.toFun ∧
      tsupport Φ.toFun⊆Cmᶜ ∧
      ∀ξ∈Cp,‖ξ‖=1 → ξ∉tsupport (fun η=>1-Φ.toFun η):=by
  let K:Set E:=Cp∩Metric.sphere 0 1
  have compactK:IsCompact K:=(isCompact_sphere (0:E) 1).inter_left closedP
  have inside:K⊆Cmᶜ:=by
    intro ξ hξ
    exact disjoint ξ hξ.1 (by simpa only [Metric.mem_sphere,dist_zero_right] using hξ.2)
  obtain ⟨δ,hδ,safe⟩:=compactK.exists_cthickening_subset_open closedM.isOpen_compl inside
  obtain ⟨ψ,smooth,compact,support,range,one⟩:=CompactSmoothCutoff.exists_cutoff
    (show IsCompact (cthickening (δ/2) K) from compactK.cthickening)
    closedM.isOpen_compl ((cthickening_mono (by linarith : δ/2≤δ) K).trans safe)
  have zero:∀ξ∈Cm,ψ ξ=0:=by
    intro ξ hξ
    by_contra nonzero
    exact support (subset_tsupport ψ (Function.mem_support.mpr nonzero)) hξ
  let Φ:AngularCutoff Cp Cm:={
    toFun:=ψ
    smoothAt_unit:=fun ξ _=>smooth.contDiffAt
    nonneg_unit:=fun ξ _=>(range ξ).1
    le_one_unit:=fun ξ _=>(range ξ).2
    one_on:=fun ξ hξ unit=>one (self_subset_cthickening K ⟨hξ,
      by simpa only [Metric.mem_sphere,dist_zero_right] using unit⟩)
    zero_on:=fun ξ hξ _=>zero ξ hξ }
  refine ⟨Φ,smooth,compact,support,?_⟩
  intro ξ hξ unit
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [isOpen_thickening.mem_nhds
    (self_subset_thickening (half_pos hδ) K ⟨hξ,
      by simpa only [Metric.mem_sphere,dist_zero_right] using unit⟩)] with η hη
  change 1-ψ η=0
  rw [one (thickening_subset_cthickening (δ/2) K hη),sub_self]

theorem exists_enlargements (closedP:IsClosed Cp) (closedM:IsClosed Cm)
    (disjoint:∀ξ∈Cp,‖ξ‖=1 → ξ∉Cm):
    ∃Φ:AngularCutoff Cp Cm,∃plus minus:E→ℝ,
      ContDiff ℝ ∞ Φ.toFun ∧ ContDiff ℝ ∞ plus ∧ ContDiff ℝ ∞ minus ∧
      HasCompactSupport plus ∧ HasCompactSupport minus ∧
      (∀ξ,0≤plus ξ ∧plus ξ≤1) ∧(∀ξ,0≤minus ξ ∧minus ξ≤1) ∧
      tsupport plus⊆Cmᶜ ∧tsupport minus⊆Cpᶜ ∧
      (∀ξ,‖ξ‖=1 → Φ.toFun ξ≠0 → plus ξ=1) ∧
      (∀ξ,‖ξ‖=1 → 1-Φ.toFun ξ≠0 → minus ξ=1):=by
  obtain ⟨Φ,smooth,_,support,collar⟩:=exists_cutoff closedP closedM disjoint
  let Kp:=tsupport Φ.toFun∩Metric.sphere (0:E) 1
  let Km:=tsupport (fun ξ=>1-Φ.toFun ξ)∩Metric.sphere (0:E) 1
  have compactP:IsCompact Kp:=(isCompact_sphere (0:E) 1).inter_left (isClosed_tsupport _)
  have compactM:IsCompact Km:=(isCompact_sphere (0:E) 1).inter_left (isClosed_tsupport _)
  have insideP:Kp⊆Cmᶜ:=fun _ h=>support h.1
  have insideM:Km⊆Cpᶜ:=by
    intro ξ hξ member
    exact collar ξ member (by simpa only [Metric.mem_sphere,dist_zero_right] using hξ.2) hξ.1
  obtain ⟨plus,hplus,cplus,splus,rplus,oplus⟩:=
    CompactSmoothCutoff.exists_cutoff compactP closedM.isOpen_compl insideP
  obtain ⟨minus,hminus,cminus,sminus,rminus,ominus⟩:=
    CompactSmoothCutoff.exists_cutoff compactM closedP.isOpen_compl insideM
  refine ⟨Φ,plus,minus,smooth,hplus,hminus,cplus,cminus,rplus,rminus,splus,sminus,?_,?_⟩
  · intro ξ unit nonzero
    exact oplus ⟨subset_tsupport _ (Function.mem_support.mpr nonzero),
      by simpa only [Metric.mem_sphere,dist_zero_right] using unit⟩
  · intro ξ unit nonzero
    exact ominus ⟨subset_tsupport _ (Function.mem_support.mpr nonzero),
      by simpa only [Metric.mem_sphere,dist_zero_right] using unit⟩
end LeanShared.ConstructedBufferedAngularCutoff
