module

public import LeanShared.Dynamics.PressureCardinalityBound
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The actual weighted separated partition supremum is positive and
finite whenever the actual separated sets satisfy a finite alphabet bound. -/
public noncomputable section
open Set Function Filter
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [Nonempty X]

theorem partitionSum_positive_finite_of_count (T : X → X) (φ : X →ᵇ ℝ)
    (n p a : ℕ) (ε : ℝ)
    (count : ∀ s : Finset X, Separated T univ n ε s → s.card ≤ a^(n+p)) :
    separatedPartitionSum T φ univ n ε ≠ 0 ∧ separatedPartitionSum T φ univ n ε ≠ ⊤ := by
  classical
  let x : X := Classical.arbitrary X
  have separated : Separated T univ n ε {x} := by
    refine ⟨fun _ _ => mem_univ _,?_⟩
    intro y hy z hz different
    exact (different ((Finset.mem_singleton.mp hy).trans (Finset.mem_singleton.mp hz).symm)).elim
  have lower : ENNReal.ofReal (Real.exp (orbitSum T φ n x)) ≤ separatedPartitionSum T φ univ n ε := by
    unfold separatedPartitionSum
    apply le_iSup_of_le {x}
    apply le_iSup_of_le separated
    simp only [Finset.sum_singleton]
    exact le_rfl
  refine ⟨ne_of_gt ((ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le lower),?_⟩
  have upper := partitionSum_bound_of_card ‖φ‖ (fun x => (le_abs_self (φ x)).trans (φ.norm_coe_le_norm x))
    a n p ε count
  exact ne_top_of_le_ne_top (by finiteness) upper

end LeanShared.ThermodynamicDefinitions
