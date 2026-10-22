module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Finite-dimensional kernels of all powers from a finite-dimensional kernel.
This is the algebraic step from finite-dimensional eigenspaces to the finite
Jordan levels used by Fredholm and Riesz theory. -/

public section
namespace LeanShared.FiniteKernelPowers
variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]

/-- Each generalized kernel is finite dimensional if the first kernel is. -/
theorem finiteDimensional (S : Module.End K E) [FiniteDimensional K S.ker] (n : ℕ) :
    FiniteDimensional K (S ^ n).ker := by
  induction n with
  | zero =>
    have hzero : (S ^ 0).ker = (⊥ : Submodule K E) := by ext x; simp
    rw [hzero]
    infer_instance
  | succ n ih =>
    let _ : FiniteDimensional K (S ^ n).ker := ih
    rw [pow_succ, Module.End.mul_eq_comp, LinearMap.ker_comp]
    infer_instance

end LeanShared.FiniteKernelPowers
