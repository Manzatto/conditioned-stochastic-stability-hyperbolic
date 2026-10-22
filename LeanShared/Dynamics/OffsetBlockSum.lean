module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Distinct residue offsets enumerate disjoint full-block starting
positions, so their combined nonnegative costs are bounded by all starts. -/
public section
open Set
open scoped BigOperators
namespace LeanShared.OffsetBlockSum

theorem le_all_starts (m n : ℕ) (positive : 0 < m) (F : ℕ → ℝ) (nonnegative : ∀ j, 0 ≤ F j) :
    (∑ r ∈ Finset.range m, ∑ j ∈ Finset.range ((n-r)/m), F (r+j*m)) ≤
      ∑ j ∈ Finset.range n, F j := by
  let s := (Finset.range m).sigma (fun r => Finset.range ((n-r)/m))
  have residue {p : (Σ _ : ℕ, ℕ)} (hp : p ∈ s) : p.1 < m :=
    Finset.mem_range.mp (Finset.mem_sigma.mp hp).1
  have injection : Set.InjOn (fun p : (Σ _ : ℕ, ℕ) => p.1+p.2*m) s := by
    intro a ha b hb equal
    have first : a.1=b.1 := by
      have congruence := congrArg (fun v => v % m) equal
      simpa only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (residue ha),Nat.mod_eq_of_lt (residue hb)] using congruence
    have second : a.2=b.2 := by
      have congruence := congrArg (fun v => v / m) equal
      simpa only [Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt (residue ha),
        Nat.div_eq_of_lt (residue hb),Nat.zero_add] using congruence
    exact Sigma.ext first (by simpa only [heq_eq_eq] using second)
  have subset : s.image (fun p : (Σ _ : ℕ, ℕ) => p.1+p.2*m) ⊆ Finset.range n := by
    intro j hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    have before := Finset.mem_range.mp (Finset.mem_sigma.mp hp).2
    have full := (Nat.le_div_iff_mul_le positive).mp (Nat.succ_le_of_lt before)
    rw [Nat.succ_mul] at full
    apply Finset.mem_range.mpr
    omega
  have bound := Finset.sum_le_sum_of_injOn (fun p : (Σ _ : ℕ, ℕ) => p.1+p.2*m)
    injection subset (fun _ _ => le_refl _) (fun j _ _ => nonnegative j)
  simpa only [s,Finset.sum_sigma] using bound

end LeanShared.OffsetBlockSum
