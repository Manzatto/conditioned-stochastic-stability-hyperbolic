module

public import LeanShared.Dynamics.OneSidedPredecessors

/-! A literal finite bilateral graph word can be attached to any admitted
future with the same endpoint symbol.  The splice retains the full word
and maps to exactly the prescribed future after the given number of
one-sided shifts.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

@[expose] def futureSplice (reference : Path R) (n : ℕ) (a : FuturePath R)
    (endpoint : reference.val n = a.val 0) : FuturePath R :=
  futureRestriction (pasteWindow reference reference (translatePath (futureExtension a) (-(n : ℤ)))
    0 n (by omega) rfl (by
      change (futureExtension a).val ((n : ℤ) + -(n : ℤ)) = reference.val n
      rw [add_neg_cancel]
      exact (futureExtension_future a 0).trans endpoint.symm))

omit [TopologicalSpace A] in
theorem futureSplice_word (reference : Path R) (n : ℕ) (a : FuturePath R)
    (endpoint : reference.val n = a.val 0) (k : ℕ) (bound : k ≤ n) :
    (futureSplice reference n a endpoint).val k = reference.val k := by
  simp only [futureSplice, futureRestriction, pasteWindow,
    ite_eq_right (by omega : ¬ (k : ℤ) < 0), ite_eq_left (by omega : (k : ℤ) ≤ n)]

omit [TopologicalSpace A] in
theorem futureSplice_tail (reference : Path R) (n : ℕ) (a : FuturePath R)
    (endpoint : reference.val n = a.val 0) (k : ℕ) :
    (futureSplice reference n a endpoint).val (k + n) = a.val k := by
  by_cases zero : k = 0
  · subst k
    rw [zero_add, futureSplice_word reference n a endpoint n le_rfl]
    exact endpoint
  · simp only [futureSplice, futureRestriction, pasteWindow, translatePath,
      Int.natCast_add, add_neg_cancel_right]
    rw [ite_eq_right (by omega : ¬ (k : ℤ) + n < 0), ite_eq_right (by omega : ¬ (k : ℤ) + n ≤ n)]
    exact futureExtension_future a k

theorem futureShift_iterate_val (a : FuturePath R) (n k : ℕ) :
    ((futureShift : FuturePath R → FuturePath R)^[n] a).val k = a.val (k + n) := by
  induction n generalizing k with
  | zero => simp only [iterate_zero_apply, Nat.add_zero]
  | succ n induction =>
    rw [iterate_succ_apply', futureShift_val, induction]
    exact congrArg a.val (by omega : k + 1 + n = k + (n + 1))

theorem futureShift_splice (reference : Path R) (n : ℕ) (a : FuturePath R)
    (endpoint : reference.val n = a.val 0) :
    (futureShift : FuturePath R → FuturePath R)^[n] (futureSplice reference n a endpoint) = a := by
  apply Subtype.ext
  funext k
  rw [futureShift_iterate_val, futureSplice_tail]

end LeanShared.BilateralShadowingCoding
