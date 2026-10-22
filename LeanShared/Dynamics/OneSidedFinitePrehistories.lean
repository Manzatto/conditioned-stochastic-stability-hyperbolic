module

public import LeanShared.Dynamics.OneSidedGraphSplicing
public import LeanShared.Dynamics.OneSidedShiftFibers

/-! Literal finite fibers of every one-sided shift iterate, with an
injective finite-word encoding and the exact successive-fiber
composition equivalence needed for weighted inverse-orbit sums.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

@[expose] def FuturePrehistory (n : ℕ) (a : FuturePath R) :=
  {b : FuturePath R // (futureShift : FuturePath R → FuturePath R)^[n] b = a}

@[expose] def futurePrehistoryWord (n : ℕ) (a : FuturePath R) (b : FuturePrehistory n a) : Fin n → A :=
  fun i => b.val.val i.val

theorem futurePrehistoryWord_injective (n : ℕ) (a : FuturePath R) :
    Injective (futurePrehistoryWord n a) := by
  intro b c equal
  apply Subtype.ext
  apply Subtype.ext
  funext k
  by_cases before : k < n
  · exact congrFun equal ⟨k, before⟩
  · have after : n ≤ k := le_of_not_gt before
    have left := congrArg (fun d : FuturePath R => d.val (k - n)) b.property
    have right := congrArg (fun d : FuturePath R => d.val (k - n)) c.property
    rw [futureShift_iterate_val, Nat.sub_add_cancel after] at left right
    exact left.trans right.symm

instance futurePrehistoryFinite [Fintype A] (n : ℕ) (a : FuturePath R) : Finite (FuturePrehistory n a) :=
  Finite.of_injective (futurePrehistoryWord n a) (futurePrehistoryWord_injective n a)

instance futurePrehistoryFintype [Fintype A] (n : ℕ) (a : FuturePath R) : Fintype (FuturePrehistory n a) :=
  Fintype.ofFinite _

@[expose] def futurePrehistoryZero (a : FuturePath R) : FuturePrehistory 0 a := ⟨a, rfl⟩

theorem futurePrehistory_zero_unique (a : FuturePath R) (b : FuturePrehistory 0 a) :
    b = futurePrehistoryZero a := by
  apply Subtype.ext
  exact b.property

@[expose] def futurePrehistorySuccEquiv (n : ℕ) (a : FuturePath R) :
    FuturePrehistory (n + 1) a ≃
      (Σ c : FuturePrehistory 1 a, FuturePrehistory n c.val) where
  toFun b :=
    ⟨⟨(futureShift : FuturePath R → FuturePath R)^[n] b.val, by
      change futureShift ((futureShift : FuturePath R → FuturePath R)^[n] b.val) = a
      have identity := b.property
      change (futureShift : FuturePath R → FuturePath R)^[n + 1] b.val = a at identity
      simpa only [iterate_succ_apply'] using identity⟩, ⟨b.val, rfl⟩⟩
  invFun c := ⟨c.2.val, by
    rw [iterate_succ_apply', c.2.property]
    exact c.1.property⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv c := by
    rcases c with ⟨⟨c, hc⟩, ⟨b, hb⟩⟩
    cases hb
    rfl

end LeanShared.BilateralShadowingCoding
