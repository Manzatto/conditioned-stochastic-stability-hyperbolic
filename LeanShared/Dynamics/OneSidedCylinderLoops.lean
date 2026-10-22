module

public import LeanShared.Dynamics.OneSidedPeriodicFutures
public import LeanShared.Dynamics.ComplexOneSidedCylinderIndicators

/-! Literal cylinder loops are actual inverse orbits of cylinder
representatives with the full matching prefix retained.  They form a
finite type, and every genuine periodic future produces such a loop.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

theorem futurePath_eq_of_initial_tail (n : ℕ) (a b : FuturePath R)
    (initial : ∀ k : ℕ, k < n → a.val k = b.val k)
    (tail : (futureShift : FuturePath R → FuturePath R)^[n] a =
      (futureShift : FuturePath R → FuturePath R)^[n] b) : a = b := by
  apply Subtype.ext
  funext k
  by_cases before : k < n
  · exact initial k before
  · have after : n ≤ k := le_of_not_gt before
    have identity := congrArg (fun c : FuturePath R => c.val (k - n)) tail
    rw [futureShift_iterate_val, futureShift_iterate_val, Nat.sub_add_cancel after] at identity
    exact identity

@[expose] def CylinderLoop (n m : ℕ) :=
  {d : RealizedPrefix R m × FuturePath R //
    (futureShift : FuturePath R → FuturePath R)^[n] d.2 = prefixRepresentative m d.1 ∧
      PrefixAgreement d.2 (prefixRepresentative m d.1) m}

@[expose] def cylinderLoopWord (n m : ℕ) (d : CylinderLoop (R := R) n m) :
    RealizedPrefix R m × (Fin n → A) := ⟨d.val.1, fun k => d.val.2.val k.val⟩

theorem cylinderLoopWord_injective (n m : ℕ) : Injective (cylinderLoopWord (R := R) n m) := by
  intro a b equal
  have symbol : a.val.1 = b.val.1 := congrArg (fun d : RealizedPrefix R m × (Fin n → A) => d.1) equal
  have word := congrArg (fun d : RealizedPrefix R m × (Fin n → A) => d.2) equal
  apply Subtype.ext
  apply Prod.ext symbol
  apply futurePath_eq_of_initial_tail n a.val.2 b.val.2
  · intro k before
    exact congrFun word ⟨k, before⟩
  · exact a.property.1.trans ((congrArg (prefixRepresentative m) symbol).trans b.property.1.symm)

instance cylinderLoopFinite [Fintype A] (n m : ℕ) : Finite (CylinderLoop (R := R) n m) :=
  Finite.of_injective (cylinderLoopWord n m) (cylinderLoopWord_injective n m)

instance cylinderLoopFintype [Fintype A] (n m : ℕ) : Fintype (CylinderLoop (R := R) n m) :=
  Fintype.ofFinite _

omit [TopologicalSpace A] in
theorem realizedPrefix_representative (m : ℕ) (w : RealizedPrefix R m) :
    realizedPrefix m (prefixRepresentative m w) = w := by
  apply Subtype.ext
  funext k
  exact Classical.choose_spec w.property k

theorem periodic_splice_matching_window (n m : ℕ) (p : PeriodicFuture (R := R) n)
    (a : FuturePath R) (same : PrefixAgreement p.val a m)
    (endpoint : (futureExtension p.val).val n = a.val 0) :
    PrefixAgreement (futureSplice (futureExtension p.val) n a endpoint) p.val (n + m) := by
  intro k bound
  by_cases before : k ≤ n
  · rw [futureSplice_word _ _ _ _ k before, futureExtension_future]
  · have after : n ≤ k := by omega
    have tailBound : k - n ≤ m := by omega
    calc
      _ = a.val (k - n) := by
        conv_lhs => rw [← Nat.sub_add_cancel after]
        exact futureSplice_tail _ _ _ _ _
      _ = p.val.val (k - n) := (same (k - n) tailBound).symm
      _ = p.val.val k := by
        simpa only [Nat.sub_add_cancel after] using (periodicFuture_repeats n p (k - n)).symm

@[expose] def periodicCylinderLoop (n m : ℕ) (p : PeriodicFuture (R := R) n) : CylinderLoop (R := R) n m := by
  let w := realizedPrefix m p.val
  let a := prefixRepresentative m w
  have same : PrefixAgreement p.val a m := prefixRepresentative_agrees m p.val
  have endpoint : (futureExtension p.val).val n = a.val 0 :=
    (futureExtension_future p.val n).trans ((periodicFuture_closed n p).trans (same 0 (by omega)))
  let b := futureSplice (futureExtension p.val) n a endpoint
  have agreement : PrefixAgreement b p.val (n + m) := periodic_splice_matching_window n m p a same endpoint
  refine ⟨(w, b), futureShift_splice (futureExtension p.val) n a endpoint, ?_⟩
  intro k bound
  exact (agreement k (by omega)).trans (same k bound)

theorem periodicCylinderLoop_window (n m : ℕ) (p : PeriodicFuture (R := R) n) :
    PrefixAgreement (periodicCylinderLoop n m p).val.2 p.val (n + m) := by
  let a := prefixRepresentative m (realizedPrefix m p.val)
  have same : PrefixAgreement p.val a m := prefixRepresentative_agrees m p.val
  have endpoint : (futureExtension p.val).val n = a.val 0 :=
    (futureExtension_future p.val n).trans ((periodicFuture_closed n p).trans (same 0 (by omega)))
  change PrefixAgreement (futureSplice (futureExtension p.val) n a endpoint) p.val (n + m)
  exact periodic_splice_matching_window n m p a same endpoint

theorem cylinderLoop_repeats (n m : ℕ) (d : CylinderLoop (R := R) n m) (k : ℕ) (bound : k ≤ m) :
    d.val.2.val (k + n) = d.val.2.val k := by
  have identity := congrArg (fun a : FuturePath R => a.val k) d.property.1
  rw [futureShift_iterate_val] at identity
  exact identity.trans (d.property.2 k bound).symm

@[expose] def cylinderLoopPeriodic (n m : ℕ) (positiveN : 0 < n) (d : CylinderLoop (R := R) n m) :
    PeriodicFuture (R := R) n := by
  have closed : d.val.2.val n = d.val.2.val 0 := by
    simpa only [zero_add] using cylinderLoop_repeats n m d 0 (by omega)
  exact ⟨periodizeFutureWord d.val.2 n positiveN closed, periodizeFutureWord_periodic _ _ _ _⟩

theorem cylinderLoopPeriodic_window (n m : ℕ) (positiveN : 0 < n) (d : CylinderLoop (R := R) n m) :
    PrefixAgreement (cylinderLoopPeriodic n m positiveN d).val d.val.2 (n + m) := by
  have closed : d.val.2.val n = d.val.2.val 0 := by
    simpa only [zero_add] using cylinderLoop_repeats n m d 0 (by omega)
  change PrefixAgreement (periodizeFutureWord d.val.2 n positiveN closed) d.val.2 (n + m)
  exact fun k bound => periodizeFutureWord_matching_window d.val.2 n positiveN closed m
    (cylinderLoop_repeats n m d) k bound

end LeanShared.BilateralShadowingCoding
