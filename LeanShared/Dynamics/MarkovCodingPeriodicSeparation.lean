module

public import LeanShared.Dynamics.MarkovCodingAffiliation
public import Mathlib.Algebra.Ring.Periodic

/-! Periodic lifts of the same point are separated by their time-zero
symbol.  The proof uses the actual finite-window no-diamonds property,
with a whole number of periods on each side of the desired coordinate.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding
variable {X I : Type*} [MetricSpace X]

theorem periodic_lifts_eq_of_symbol_eq (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code)
    (a b : Path (Transition T rectangles)) (samePoint : code a = code b)
    (p : ℕ) (positive : 0 < p)
    (periodicA : Function.Periodic a.val (p : ℤ))
    (periodicB : Function.Periodic b.val (p : ℤ))
    (sameSymbol : a.val 0 = b.val 0) : a = b := by
  apply Subtype.ext
  funext k
  let m := k.natAbs + 1
  let radius := m * p
  have startA : a.val (-(radius : ℤ)) = a.val 0 := by
    simpa only [radius, Nat.cast_mul] using (periodicA.neg_nat_mul m).eq
  have startB : b.val (-(radius : ℤ)) = b.val 0 := by
    simpa only [radius, Nat.cast_mul] using (periodicB.neg_nat_mul m).eq
  have endA : a.val (radius : ℤ) = a.val 0 := by
    simpa only [radius, Nat.cast_mul] using periodicA.nat_mul_eq m
  have endB : b.val (radius : ℤ) = b.val 0 := by
    simpa only [radius, Nat.cast_mul] using periodicB.nat_mul_eq m
  have large : k.natAbs ≤ radius := by
    have bound : m ≤ m * p := Nat.le_mul_of_pos_right m positive
    dsimp only [m] at bound
    exact (Nat.le_succ _).trans bound
  exact geometry.2 a b samePoint radius (startA.trans (sameSymbol.trans startB.symm))
    (endA.trans (sameSymbol.trans endB.symm)) k (by omega) (by omega)

end LeanShared.MarkovFinitePathRealization
