module

public import LeanShared.Dynamics.RobustFiniteIsolation

/-! A single fixed number of initial/final steps removes the transient
part of every finite surviving orbit: all remaining points are in any
prescribed open neighborhood of the literal two-sided isolated core. -/
public section
namespace LeanShared
open Set Function

 theorem exists_uniform_middle_core_neighborhood {X : Type*} [TopologicalSpace X]
    [T2Space X] (T : X ≃ₜ X) {K U : Set X}
    (compact : IsCompact K) (openU : IsOpen U) (core : isolatedCore T K ⊆ U) :
    ∃ L : ℕ, 0 < L ∧ ∀ n : ℕ, ∀ y : X,
      (∀ j ≤ n + 2*L, (T : X → X)^[j] y ∈ K) →
      ∀ j ≤ n, (T : X → X)^[L+j] y ∈ U := by
  obtain ⟨L, positive, capture⟩ := exists_pos_finite_isolation T compact openU core
  refine ⟨L, positive, fun n y survives j hj => ?_⟩
  apply capture
  · intro k hk
    rw [← Function.iterate_add_apply]
    exact survives (k+(L+j)) (by omega)
  · intro k hk
    have length : L+j = k+(L+j-k) := by omega
    rw [length, Function.iterate_add_apply]
    have inverse : Function.LeftInverse (T.symm : X → X) (T : X → X) := T.symm_apply_apply
    rw [inverse.iterate k]
    exact survives (L+j-k) (by omega)

end LeanShared
