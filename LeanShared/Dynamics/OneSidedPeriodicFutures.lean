module

public import LeanShared.Dynamics.OneSidedWordPeriodization

/-! Literal periodic futures are determined by their first positive
period-length word.  Their finite enumeration retains the exact shift
fixed-point condition, and every coordinate is its word's periodic repeat.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

@[expose] def PeriodicFuture (n : ℕ) :=
  {a : FuturePath R // (futureShift : FuturePath R → FuturePath R)^[n] a = a}

theorem periodicFuture_repeats (n : ℕ) (a : PeriodicFuture (R := R) n) (k : ℕ) :
    a.val.val (k + n) = a.val.val k := by
  have identity := congrArg (fun b : FuturePath R => b.val k) a.property
  rw [futureShift_iterate_val] at identity
  exact identity

theorem periodicFuture_closed (n : ℕ) (a : PeriodicFuture (R := R) n) :
    a.val.val n = a.val.val 0 := by simpa only [zero_add] using periodicFuture_repeats n a 0

theorem periodicFuture_mod (n : ℕ) (positiveN : 0 < n) (a : PeriodicFuture (R := R) n) (k : ℕ) :
    a.val.val k = a.val.val (k % n) := by
  have agreement := periodizeFutureWord_matching_window a.val n positiveN (periodicFuture_closed n a) k
    (fun j _ => periodicFuture_repeats n a j) k (by omega)
  rw [periodizeFutureWord_val] at agreement
  exact agreement.symm

@[expose] def periodicFutureWord (n : ℕ) (a : PeriodicFuture (R := R) n) : Fin n → A :=
  fun k => a.val.val k.val

theorem periodicFutureWord_injective (n : ℕ) (positiveN : 0 < n) :
    Injective (periodicFutureWord (R := R) n) := by
  intro a b equal
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [periodicFuture_mod n positiveN a k, periodicFuture_mod n positiveN b k]
  exact congrFun equal ⟨k % n, Nat.mod_lt k positiveN⟩

instance periodicFutureFinite [Fintype A] (n : ℕ) [NeZero n] : Finite (PeriodicFuture (R := R) n) :=
  Finite.of_injective (periodicFutureWord n)
    (periodicFutureWord_injective n (Nat.pos_of_ne_zero (NeZero.ne n)))

instance periodicFutureFintype [Fintype A] (n : ℕ) [NeZero n] : Fintype (PeriodicFuture (R := R) n) :=
  Fintype.ofFinite _

end LeanShared.BilateralShadowingCoding
