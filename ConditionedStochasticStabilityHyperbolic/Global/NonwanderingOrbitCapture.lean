module
public import ConditionedStochasticStabilityHyperbolic.Paper.GlobalHypotheses
public import Mathlib.Order.Filter.Finite

/-! Every orbit on a compact space eventually stays in each prescribed
neighborhood of the actual nonwandering set. This uses finite wandering
covers, with no recurrence or orbit-limit source. -/
public section
open Set Filter Function
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.NonwanderingOrbitCapture
variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
private theorem avoids (T : X → X) (U : Set X)
    (wandering : ∀ n, 0<n → ∀ y∈U, T^[n] y∉U) (x : X) :
    ∀ᶠ n : ℕ in atTop, T^[n] x∉U := by
  by_cases visit : ∃ j, T^[j] x∈U
  · obtain ⟨j,hj⟩ := visit
    filter_upwards [eventually_ge_atTop (j+1)] with n hn
    have h := wandering (n-j) (by omega) (T^[j] x) hj
    simpa only [← iterate_add_apply,Nat.sub_add_cancel (show j≤n by omega)] using h
  · exact Eventually.of_forall fun n hn => visit ⟨n,hn⟩

theorem eventually_in_neighborhood [CompactSpace X] (T : X → X) {O : Set X}
    (openO : IsOpen O) (contains : Paper.nonwanderingSet T ⊆ O) (x : X) :
    ∀ᶠ n : ℕ in atTop, T^[n] x∈O := by
  classical
  have wandering (y : ↥(Oᶜ)) : ∃ U : Set X, IsOpen U ∧ y.val∈U ∧
      ∀ n, 0<n → ∀ z∈U, T^[n] z∉U := by
    have outside : y.val∉Paper.nonwanderingSet T := fun h => y.property (contains h)
    change ¬ (∀ U : Set X, IsOpen U → y.val∈U →
      ∃ n : ℕ, 0<n ∧ ∃ z∈U, T^[n] z∈U) at outside
    push Not at outside
    exact outside
  choose U openU member free using wandering
  obtain ⟨s,cover⟩ := openO.isClosed_compl.isCompact.elim_finite_subcover
    U openU (fun y hy => mem_iUnion.mpr ⟨⟨y,hy⟩,member ⟨y,hy⟩⟩)
  have escape : ∀ᶠ n : ℕ in atTop, ∀ y∈s, T^[n] x∉U y :=
    s.eventually_all.mpr fun y _ => avoids T (U y) (free y) x
  filter_upwards [escape] with n hn
  by_contra outside
  obtain ⟨y,hy,hit⟩ := mem_iUnion₂.mp (cover outside)
  exact hn y hy hit
end ConditionedStochasticStabilityHyperbolic.Global.NonwanderingOrbitCapture
