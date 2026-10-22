module
public import Mathlib.Data.Int.Basic
public import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! Exact finite forward times in a backward-indexed entire orbit. -/
public section
namespace LeanShared.EntireOrbitFiniteTimes
open Function
variable {X:Type*}

theorem iterate_between (T:X→X) (p:ℤ→X) (step:∀j,T (p (j+1))=p j) (m n:ℕ) :
    (T^[n]) (p ((m+n:ℕ):ℤ))=p (m:ℤ) := by
  induction n with
  | zero => simp only [Nat.add_zero,iterate_zero,id_eq]
  | succ n ih =>
    rw [iterate_succ_apply]
    have index:((m+(n+1):ℕ):ℤ)=((m+n:ℕ):ℤ)+1 := by omega
    rw [index,step]
    exact ih

end LeanShared.EntireOrbitFiniteTimes
