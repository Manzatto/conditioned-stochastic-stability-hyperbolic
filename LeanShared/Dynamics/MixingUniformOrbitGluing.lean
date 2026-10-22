module
public import LeanShared.Dynamics.HyperbolicBasicSet
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

/-! Compactness upgrades literal topological mixing to one common orbit
transition time for all pairs of points, at each prescribed metric accuracy. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Function
variable {X:Type*} [MetricSpace X] {T:X≃ₜX} {K:Set X}

theorem MixingOn.uniform_orbit_hits (mixing:MixingOn T K) (compact:IsCompact K)
    (ε:ℝ) (positive:0<ε) :
    ∃N:ℕ,∀n≥N,∀x∈K,∀y∈K,∃z∈K,
      dist z x<ε ∧ dist (((T:X→X)^[n]) z) y<ε := by
  classical
  obtain ⟨centers,cover⟩ := compact.elim_finite_subcover (fun x:K=>Metric.ball x.val (ε/2))
    (fun _=>Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,by simpa only [Metric.mem_ball,dist_self] using half_pos positive⟩)
  have pair (p:K×K) : ∃N:ℕ,∀n≥N,∃z∈K∩Metric.ball p.1.val (ε/2),
      ((T:X→X)^[n]) z∈Metric.ball p.2.val (ε/2) := by
    apply mixing _ _ Metric.isOpen_ball Metric.isOpen_ball
    · exact ⟨p.1.val,p.1.property,by simpa only [Metric.mem_ball,dist_self] using half_pos positive⟩
    · exact ⟨p.2.val,p.2.property,by simpa only [Metric.mem_ball,dist_self] using half_pos positive⟩
  choose waiting hits using pair
  let N := (centers×ˢcenters).sup waiting
  refine ⟨N,fun n hn x hx y hy=>?_⟩
  obtain ⟨cx,hcx,nearX⟩ := mem_iUnion₂.mp (cover hx)
  obtain ⟨cy,hcy,nearY⟩ := mem_iUnion₂.mp (cover hy)
  have pairMember : (cx,cy)∈centers×ˢcenters := Finset.mem_product.mpr ⟨hcx,hcy⟩
  have waitBound : waiting (cx,cy)≤n := (Finset.le_sup pairMember).trans hn
  obtain ⟨z,hz,nearEnd⟩ := hits (cx,cy) n waitBound
  refine ⟨z,hz.1,?_,?_⟩
  · have a : dist z cx.val<ε/2 := hz.2
    have b : dist cx.val x<ε/2 := by simpa only [Metric.mem_ball,dist_comm] using nearX
    exact (dist_triangle z cx.val x).trans_lt (by linarith)
  · have a : dist (((T:X→X)^[n]) z) cy.val<ε/2 := nearEnd
    have b : dist cy.val y<ε/2 := by simpa only [Metric.mem_ball,dist_comm] using nearY
    exact (dist_triangle _ cy.val y).trans_lt (by linarith)

end LeanShared.HyperbolicBasicSet
