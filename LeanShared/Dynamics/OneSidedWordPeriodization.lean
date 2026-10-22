module

public import LeanShared.Dynamics.OneSidedFutureEdgeConstruction
public import LeanShared.Dynamics.OneSidedFinitePrehistories

/-! An actual closed finite graph word gives a literal periodic future.
A matching-prefix inverse orbit agrees with this periodization through
the whole inverse-orbit length plus the retained cylinder window.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

omit [TopologicalSpace A] in
theorem closedFutureWord_edges (b : FuturePath R) (n : ℕ) (positiveN : 0 < n)
    (closed : b.val n = b.val 0) (k : ℕ) : R (b.val (k % n)) (b.val ((k + 1) % n)) := by
  have nextMod : (k + 1) % n = (k % n + 1) % n := by
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.mod_mod]
  rw [nextMod]
  by_cases inside : k % n + 1 < n
  · rw [Nat.mod_eq_of_lt inside]
    exact futurePath_edge b (k % n)
  · have boundary : k % n + 1 = n := by have bound := Nat.mod_lt k positiveN; omega
    rw [boundary, Nat.mod_self]
    have edge := futurePath_edge b (k % n)
    rw [boundary, closed] at edge
    exact edge

@[expose] def periodizeFutureWord (b : FuturePath R) (n : ℕ) (positiveN : 0 < n)
    (closed : b.val n = b.val 0) : FuturePath R :=
  admittedFutureOfEdges (fun k => b.val (k % n)) (closedFutureWord_edges b n positiveN closed)
    (futureExtension b) (by simpa only [Nat.zero_mod, Int.natCast_zero] using futureExtension_future b 0)

omit [TopologicalSpace A] in
theorem periodizeFutureWord_val (b : FuturePath R) (n : ℕ) (positiveN : 0 < n)
    (closed : b.val n = b.val 0) (k : ℕ) :
    (periodizeFutureWord b n positiveN closed).val k = b.val (k % n) := rfl

omit [TopologicalSpace A] in
theorem periodizeFutureWord_initial (b : FuturePath R) (n : ℕ) (positiveN : 0 < n)
    (closed : b.val n = b.val 0) (k : ℕ) (before : k < n) :
    (periodizeFutureWord b n positiveN closed).val k = b.val k := by
  rw [periodizeFutureWord_val, Nat.mod_eq_of_lt before]

theorem periodizeFutureWord_periodic (b : FuturePath R) (n : ℕ) (positiveN : 0 < n)
    (closed : b.val n = b.val 0) :
    (futureShift : FuturePath R → FuturePath R)^[n] (periodizeFutureWord b n positiveN closed) =
      periodizeFutureWord b n positiveN closed := by
  apply Subtype.ext
  funext k
  rw [futureShift_iterate_val, periodizeFutureWord_val, periodizeFutureWord_val, Nat.add_mod_right]

theorem periodizeFutureWord_matching_window (b : FuturePath R) (n : ℕ) (positiveN : 0 < n)
    (closed : b.val n = b.val 0) (m : ℕ)
    (repeats : ∀ k : ℕ, k ≤ m → b.val (k + n) = b.val k)
    (k : ℕ) (bound : k ≤ n + m) :
    (periodizeFutureWord b n positiveN closed).val k = b.val k := by
  induction k using Nat.strong_induction_on with
  | h k induction =>
    by_cases before : k < n
    · exact periodizeFutureWord_initial b n positiveN closed k before
    · have after : n ≤ k := le_of_not_gt before
      have smaller : k - n < k := by omega
      have lowerBound : k - n ≤ n + m := by omega
      have repeatBound : k - n ≤ m := by omega
      have period := congrArg (fun a : FuturePath R => a.val (k - n))
        (periodizeFutureWord_periodic b n positiveN closed)
      rw [futureShift_iterate_val, Nat.sub_add_cancel after] at period
      calc
        _ = (periodizeFutureWord b n positiveN closed).val (k - n) := period
        _ = b.val (k - n) := induction (k - n) smaller lowerBound
        _ = b.val k := by simpa only [Nat.sub_add_cancel after] using (repeats (k - n) repeatBound).symm

theorem futurePrehistory_matching_repeats (n m : ℕ) (a : FuturePath R) (b : FuturePrehistory n a)
    (same : PrefixAgreement b.val a m) (k : ℕ) (bound : k ≤ m) :
    b.val.val (k + n) = b.val.val k := by
  have tail := congrArg (fun c : FuturePath R => c.val k) b.property
  rw [futureShift_iterate_val] at tail
  exact tail.trans (same k bound).symm

end LeanShared.BilateralShadowingCoding
