module

public import LeanShared.LinearAlgebra.StableKernelRange
public import LeanShared.LinearAlgebra.FiniteKernelPowers
import Lean.Elab.Tactic.Omega

/-! Finite ascent and descent give a genuine Fitting decomposition in an
arbitrary module, with all later kernels and ranges explicitly stabilized. -/

public section
namespace LeanShared.FiniteFittingDecomposition
variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]

/-- Finite ascent and descent suffice for the Fitting decomposition; the
ambient module is not required to be finite dimensional. -/
theorem exists_decomposition (S : Module.End K E)
    (ascent : ∃ a : ℕ, (S ^ a).ker = (S ^ (a + 1)).ker)
    (descent : ∃ b : ℕ, (S ^ b).range = (S ^ (b + 1)).range) :
    ∃ n : ℕ, IsCompl (S ^ n).ker (S ^ n).range ∧
      (∀ m : ℕ, (S ^ (n + m)).ker = (S ^ n).ker) ∧
      (∀ m : ℕ, (S ^ (n + m)).range = (S ^ n).range) := by
  obtain ⟨a, ha⟩ := ascent
  obtain ⟨b, hb⟩ := descent
  let n := a + b
  have kernels (m : ℕ) : (S ^ (n + m)).ker = (S ^ n).ker := by
    have hleft := (Module.End.ker_pow_constant ha (b + m)).symm
    have hright := (Module.End.ker_pow_constant ha b).symm
    have heq : a + (b + m) = n + m := by dsimp only [n]; omega
    rw [heq] at hleft
    exact hleft.trans hright.symm
  have ranges (m : ℕ) : (S ^ (n + m)).range = (S ^ n).range := by
    have hleft := StableKernelRange.range_pow_constant S hb (a + m)
    have hright := StableKernelRange.range_pow_constant S hb a
    have heq : b + (a + m) = n + m := by dsimp only [n]; omega
    have heq' : b + a = n := by dsimp only [n]; omega
    rw [heq] at hleft
    rw [heq'] at hright
    exact hleft.trans hright.symm
  exact ⟨n, StableKernelRange.isCompl S n (kernels n) (ranges n), kernels, ranges⟩

end LeanShared.FiniteFittingDecomposition
