module

public import LeanShared.Dynamics.ExpansivePeriodicSeparation
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

/-! Compact expansivity makes every positive-period fixed-point set
finite, by an actual finite observation code on one forward period. -/
public noncomputable section
namespace LeanShared.ExpansivePeriodicSeparation
open Function Set Metric
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 800000 in
theorem finite (T : X ≃ₜ X) (K : Set X) (compact : IsCompact K)
    (invariant : MapsTo T K K) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (p : ℕ) (positiveP : 0 < p) :
    {x : X | x ∈ K ∧ (T : X → X)^[p] x = x}.Finite := by
  classical
  obtain ⟨centers, _, finiteCenters, cover⟩ := compact.finite_cover_balls (half_pos positiveC)
  let _ : Fintype centers := finiteCenters.fintype
  have nearby (x : K) : ∃ y : centers, dist x.val y.val < c / 2 := by
    obtain ⟨y, hy⟩ := mem_iUnion.mp (cover x.property)
    obtain ⟨member, near⟩ := mem_iUnion.mp hy
    exact ⟨⟨y, member⟩, near⟩
  choose label near using nearby
  have mesh (x y : K) (same : label x = label y) : dist x.val y.val ≤ c := by
    have first := near x
    have second := near y
    rw [← same] at second
    have triangle := dist_triangle x.val (label x).val y.val
    rw [dist_comm (label x).val y.val] at triangle
    linarith
  let P := {x : X // x ∈ K ∧ (T : X → X)^[p] x = x}
  let code : P → Fin p → centers := fun x j =>
    label ⟨(T : X → X)^[j.val] x.val, invariant.iterate j.val x.property.1⟩
  have injective : Injective code := by
    intro x y same
    apply Subtype.ext
    apply one_period_detects T K c expansive p positiveP x.val x.property.1 y.val y.property.1
      x.property.2 y.property.2
    intro j hj
    exact mesh ⟨_, invariant.iterate j x.property.1⟩ ⟨_, invariant.iterate j y.property.1⟩
      (congrFun same ⟨j, hj⟩)
  exact Set.finite_coe_iff.mp (show Finite P from Finite.of_injective code injective)

end LeanShared.ExpansivePeriodicSeparation
