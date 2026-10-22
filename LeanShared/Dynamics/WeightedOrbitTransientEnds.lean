module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Tactic.Ring

/-! Removing a fixed prefix and suffix from a bounded nonnegative orbit
weight costs a length-independent factor. -/
public noncomputable section
namespace LeanShared.WeightedOrbitTransientEnds
open scoped BigOperators

 theorem product_bound {X : Type*} (T : X → X) (g : X → ℝ)
    (nonnegative : ∀ x, 0 ≤ g x) (G : ℝ) (positiveG : 0 ≤ G)
    (bounded : ∀ x, g x ≤ G) (L n : ℕ) (y : X) :
    (∏ j ∈ Finset.range (n+2*L+1), g (T^[j] y)) ≤
      G^(2*L+1) * ∏ j ∈ Finset.range n, g (T^[j] (T^[L] y)) := by
  have length : n+2*L+1 = L+(n+(L+1)) := by omega
  rw [length, Finset.prod_range_add, Finset.prod_range_add]
  have initial : (∏ j ∈ Finset.range L, g (T^[j] y)) ≤ G^L := by
    simpa using Finset.prod_le_prod₀ (s := Finset.range L) (fun j _ => nonnegative (T^[j] y)) (fun j _ => bounded (T^[j] y))
  have final : (∏ j ∈ Finset.range (L+1), g (T^[L+(n+j)] y)) ≤ G^(L+1) := by
    simpa using Finset.prod_le_prod₀ (s := Finset.range (L+1)) (fun j _ => nonnegative (T^[L+(n+j)] y))
      (fun j _ => bounded (T^[L+(n+j)] y))
  have middleNonnegative : 0 ≤ ∏ j ∈ Finset.range n, g (T^[L+j] y) :=
    Finset.prod_nonneg (fun j _ => nonnegative _)
  have endNonnegative : 0 ≤ ∏ j ∈ Finset.range (L+1), g (T^[L+(n+j)] y) :=
    Finset.prod_nonneg (fun j _ => nonnegative _)
  have estimate := mul_le_mul initial
    (mul_le_mul_of_nonneg_left final middleNonnegative)
    (mul_nonneg middleNonnegative endNonnegative) (pow_nonneg positiveG L)
  have middle : (∏ j ∈ Finset.range n, g (T^[L+j] y)) =
      ∏ j ∈ Finset.range n, g (T^[j] (T^[L] y)) := by
    apply Finset.prod_congr rfl
    intro j _
    rw [Nat.add_comm L j, Function.iterate_add_apply]
  rw [middle] at estimate
  rw [middle]
  convert estimate using 1; simp only [pow_add, pow_one]; ring

end LeanShared.WeightedOrbitTransientEnds
