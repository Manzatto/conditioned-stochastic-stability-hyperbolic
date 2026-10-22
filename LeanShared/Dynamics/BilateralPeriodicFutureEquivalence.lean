module

public import LeanShared.Dynamics.OneSidedPeriodicCohomology
public import LeanShared.Dynamics.OneSidedPeriodicFutures
public import Mathlib.Data.Int.DivMod

/-! Restriction to the future is a literal bijection on periodic graph
paths.  The inverse is the explicit integer-periodic extension, so the
one-sided transfer coefficients retain the original bilateral orbits.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

@[expose] def PeriodicBilateral (n : ℕ) :=
  {a : Path R // (shift R : Path R → Path R)^[n] a = a}

theorem periodicBilateral_periodic (n : ℕ) (a : PeriodicBilateral (R := R) n) :
    Function.Periodic a.val.val (n : ℤ) := by
  intro k
  have coordinate := congrArg (fun b : Path R => b.val k) a.property
  rw [shift_iterate_val] at coordinate
  exact coordinate

theorem periodicBilateral_mod (n : ℕ) (a : PeriodicBilateral (R := R) n) (k : ℤ) :
    a.val.val (k % (n : ℤ)) = a.val.val k := by
  rw [Int.emod_def]
  simpa only [Int.cast_id, mul_comm] using (periodicBilateral_periodic n a).sub_int_mul_eq (x := k) (k / (n : ℤ))

theorem integer_periodic_successor_mod (n : ℕ) (positiveN : 0 < n) (k : ℤ) :
    ((k + 1) % (n : ℤ)).toNat = ((k % (n : ℤ)).toNat + 1) % n := by
  have nonzero : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positiveN
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ nonzero), Int.natCast_mod,
    Int.natCast_add, Int.natCast_one, Int.toNat_of_nonneg (Int.emod_nonneg _ nonzero)]
  exact (Int.emod_add_emod k (n : ℤ) 1).symm

@[expose] def periodicFutureBilateralExtension (n : ℕ) (positiveN : 0 < n)
    (p : PeriodicFuture (R := R) n) : Path R := by
  refine ⟨fun k => p.val.val (k % (n : ℤ)).toNat, ?_⟩
  intro k
  change R (p.val.val (k % (n : ℤ)).toNat) (p.val.val ((k + 1) % (n : ℤ)).toNat)
  rw [integer_periodic_successor_mod n positiveN k,
    ← periodicFuture_mod n positiveN p ((k % (n : ℤ)).toNat + 1)]
  exact futurePath_edge p.val _

theorem periodicFutureBilateralExtension_future (n : ℕ) (positiveN : 0 < n)
    (p : PeriodicFuture (R := R) n) :
    futureRestriction (periodicFutureBilateralExtension n positiveN p) = p.val := by
  apply Subtype.ext
  funext k
  change p.val.val ((k : ℤ) % (n : ℤ)).toNat = p.val.val k
  rw [← Int.natCast_mod, Int.toNat_natCast]
  exact (periodicFuture_mod n positiveN p k).symm

theorem periodicFutureBilateralExtension_periodic (n : ℕ) (positiveN : 0 < n)
    (p : PeriodicFuture (R := R) n) :
    (shift R : Path R → Path R)^[n] (periodicFutureBilateralExtension n positiveN p) =
      periodicFutureBilateralExtension n positiveN p := by
  apply Subtype.ext
  funext k
  rw [shift_iterate_val]
  change p.val.val ((k + n) % (n : ℤ)).toNat = p.val.val (k % (n : ℤ)).toNat
  rw [Int.add_emod_right]

@[expose] def periodicBilateralFutureEquiv (n : ℕ) (positiveN : 0 < n) :
    PeriodicBilateral (R := R) n ≃ PeriodicFuture (R := R) n where
  toFun a := ⟨futureRestriction a.val, futureRestriction_periodic n a.val a.property⟩
  invFun p := ⟨periodicFutureBilateralExtension n positiveN p,
    periodicFutureBilateralExtension_periodic n positiveN p⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    change a.val.val (((k % (n : ℤ)).toNat : ℕ) : ℤ) = a.val.val k
    have nonzero : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positiveN
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ nonzero)]
    exact periodicBilateral_mod n a k
  right_inv p := by
    apply Subtype.ext
    exact periodicFutureBilateralExtension_future n positiveN p

instance periodicBilateralFinite [Fintype A] (n : ℕ) [NeZero n] :
    Finite (PeriodicBilateral (R := R) n) :=
  Finite.of_injective (periodicBilateralFutureEquiv n (Nat.pos_of_ne_zero (NeZero.ne n)))
    (Equiv.injective _)

instance periodicBilateralFintype [Fintype A] (n : ℕ) [NeZero n] :
    Fintype (PeriodicBilateral (R := R) n) := Fintype.ofFinite _

end LeanShared.BilateralShadowingCoding
