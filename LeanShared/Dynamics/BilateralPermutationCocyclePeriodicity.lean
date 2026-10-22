module

public import LeanShared.Dynamics.BilateralPermutationCocycle

/-! Periodic matching permutations give literal bilateral monodromy of
the index transport.  The proof establishes uniqueness of the entire
integer recurrence, including cancellation at negative times.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
variable {J : Type*}

theorem indexTransport_zero (π : ℤ → Equiv.Perm J) : indexTransport π 0 = Equiv.refl J := rfl

theorem permutation_recurrence_unique (π : ℤ → Equiv.Perm J) (f g : ℤ → Equiv.Perm J)
    (stepF : ∀ n, f (n + 1) = (f n).trans (π n).symm)
    (stepG : ∀ n, g (n + 1) = (g n).trans (π n).symm)
    (initial : f 0 = g 0) : f = g := by
  funext n
  induction n using Int.induction_on with
  | zero => exact initial
  | succ n induction => rw [stepF, stepG, induction]
  | pred n induction =>
    have first := stepF (-(n : ℤ) - 1)
    have second := stepG (-(n : ℤ) - 1)
    rw [sub_add_cancel] at first second
    have equal := first.symm.trans (induction.trans second)
    apply Equiv.ext
    intro i
    exact (π (-(n : ℤ) - 1)).symm.injective
      (congrArg (fun p : Equiv.Perm J => p i) equal)

theorem indexTransport_periodic (π : ℤ → Equiv.Perm J) (period : ℤ)
    (periodic : Function.Periodic π period) (n : ℤ) :
    indexTransport π (n + period) = (indexTransport π period).trans (indexTransport π n) := by
  have equal := permutation_recurrence_unique π
    (fun j => indexTransport π (j + period))
    (fun j => (indexTransport π period).trans (indexTransport π j))
    (fun j => by
      rw [show j + 1 + period = (j + period) + 1 by omega, indexTransport_step, periodic j])
    (fun j => by rw [indexTransport_step, Equiv.trans_assoc])
    (by rw [zero_add, indexTransport_zero, Equiv.trans_refl])
  exact congrFun equal n

end LeanShared.BilateralShadowingCoding
