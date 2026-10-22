module
public import LeanShared.Dynamics.BilateralHomeomorphismOrbit
import Mathlib.Tactic.Ring

/-! Backward-indexed bilateral orbits are determined by their time-zero
point. Integer block times coincide exactly with powers of the map. -/
public section
namespace LeanShared.BilateralHomeomorphismOrbit
variable {X:Type*} [TopologicalSpace X]

theorem eq_of_initial (F:X≃ₜX) (p q:ℤ→X)
    (hp:∀n,F (p (n+1))=p n) (hq:∀n,F (q (n+1))=q n)
    (initial:p 0=q 0) : p=q := by
  funext n
  induction n using Int.induction_on with
  | zero => exact initial
  | succ n ih =>
    apply F.injective
    rw [hp,hq,ih]
  | pred n ih =>
    have left := hp (-(n:ℤ)-1)
    have right := hq (-(n:ℤ)-1)
    rw [sub_add_cancel] at left right
    convert left.symm.trans ((congrArg F ih).trans right) using 1

theorem eq_canonical (F:X≃ₜX) (p:ℤ→X) (step:∀n,F (p (n+1))=p n) :
    p=orbit F (p 0) :=
  eq_of_initial F p (orbit F (p 0)) step (fun n=>BilateralHomeomorphismOrbit.step F (p 0) n)
    (zero F (p 0)).symm

theorem block_time (T:X≃ₜX) (N:ℕ) (x:X) (n:ℤ) :
    orbit (T^N) x n=orbit T x (n*(N:ℤ)) := by
  dsimp only [orbit]
  rw [←zpow_natCast T N,←zpow_mul]
  have exponent : (N:ℤ)*(-n)=-(n*(N:ℤ)) := by ring
  rw [exponent]

theorem add_nat_time (T:X≃ₜX) (x:X) (n:ℤ) (r:ℕ) :
    orbit T x (n+(r:ℤ))=(T.symm:X→X)^[r] (orbit T x n) := by
  rw [←nat_time]
  dsimp only [orbit]
  change (T^(-(n+(r:ℤ)))) x=(T^(-(r:ℤ))*T^(-n)) x
  rw [←zpow_add]
  have exponent : -(n+(r:ℤ))=(-(r:ℤ))+(-n) := by ring
  rw [exponent]

end LeanShared.BilateralHomeomorphismOrbit
