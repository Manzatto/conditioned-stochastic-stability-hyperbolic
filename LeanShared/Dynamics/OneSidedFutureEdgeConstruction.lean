module

public import LeanShared.Dynamics.OneSidedGraphPaths

/-! Any actual natural graph path beginning at an admitted symbol gives
an admitted future, by attaching a genuine bilateral past with the same
initial symbol.  The resulting future retains every natural coordinate.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

@[expose] def bilateralFutureEdges (s : ℕ → A) (edges : ∀ k, R (s k) (s (k + 1)))
    (reference : Path R) (initial : reference.val 0 = s 0) : Path R :=
  ⟨fun k => if k < 0 then reference.val k else s k.toNat, by
    intro k
    by_cases negative : k < 0
    · by_cases nextNegative : k + 1 < 0
      · simpa only [ite_eq_left negative, ite_eq_left nextNegative] using reference.property k
      · have boundary : k + 1 = 0 := by omega
        simp only [ite_eq_left negative, ite_eq_right nextNegative]
        rw [boundary, Int.toNat_zero, ← initial]
        simpa only [boundary] using reference.property k
    · have nextNonnegative : ¬k + 1 < 0 := by omega
      simp only [ite_eq_right negative, ite_eq_right nextNonnegative]
      have nextIndex : (k + 1).toNat = k.toNat + 1 := by omega
      rw [nextIndex]
      exact edges k.toNat⟩

@[expose] def admittedFutureOfEdges (s : ℕ → A) (edges : ∀ k, R (s k) (s (k + 1)))
    (reference : Path R) (initial : reference.val 0 = s 0) : FuturePath R :=
  ⟨s, bilateralFutureEdges s edges reference initial, fun n => by
    change (if (n : ℤ) < 0 then reference.val n else s (n : ℤ).toNat) = s n
    rw [ite_eq_right (by omega : ¬ (n : ℤ) < 0), Int.toNat_natCast]⟩

omit [TopologicalSpace A] in
theorem admittedFutureOfEdges_val (s : ℕ → A) (edges : ∀ k, R (s k) (s (k + 1)))
    (reference : Path R) (initial : reference.val 0 = s 0) (n : ℕ) :
    (admittedFutureOfEdges s edges reference initial).val n = s n := rfl

end LeanShared.BilateralShadowingCoding
