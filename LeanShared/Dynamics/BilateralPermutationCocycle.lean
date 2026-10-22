module

public import LeanShared.Dynamics.SignedSubsetMatchingGraph

/-! A bilateral sequence of finite matching permutations has a literal
index transport at every integer time.  This supplies actual path lifts
of the unordered matching graph, including negative times.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
variable {J : Type*}

@[expose] def forwardIndexTransport (π : ℤ → Equiv.Perm J) : ℕ → Equiv.Perm J
  | 0 => Equiv.refl J
  | n + 1 => (forwardIndexTransport π n).trans (π n).symm

@[expose] def backwardIndexTransport (π : ℤ → Equiv.Perm J) : ℕ → Equiv.Perm J
  | 0 => Equiv.refl J
  | n + 1 => (backwardIndexTransport π n).trans (π (-(n : ℤ) - 1))

@[expose] def indexTransport (π : ℤ → Equiv.Perm J) : ℤ → Equiv.Perm J
  | .ofNat n => forwardIndexTransport π n
  | .negSucc n => backwardIndexTransport π (n + 1)

theorem indexTransport_neg_nat (π : ℤ → Equiv.Perm J) (n : ℕ) :
    indexTransport π (-(n : ℤ)) = backwardIndexTransport π n := by
  cases n <;> rfl

theorem indexTransport_step (π : ℤ → Equiv.Perm J) (n : ℤ) :
    indexTransport π (n + 1) = (indexTransport π n).trans (π n).symm := by
  cases n with
  | ofNat n => rfl
  | negSucc n =>
    have atTime : (Int.negSucc n : ℤ) = -(n : ℤ) - 1 := by omega
    have next : (Int.negSucc n : ℤ) + 1 = -(n : ℤ) := by omega
    rw [next, indexTransport_neg_nat]
    change backwardIndexTransport π n = (backwardIndexTransport π (n + 1)).trans (π (Int.negSucc n)).symm
    rw [backwardIndexTransport, atTime]
    simp only [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl]

end LeanShared.BilateralShadowingCoding
