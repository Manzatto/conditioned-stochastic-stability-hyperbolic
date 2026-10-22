module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Fitting decomposition from finite stabilization of kernels and ranges,
without a finite-dimensionality hypothesis on the ambient module. -/

public section
namespace LeanShared.StableKernelRange
variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]

/-- Once two consecutive ranges agree, all later ranges agree. -/
theorem range_pow_constant (S : Module.End K E) {k : ℕ}
    (h : (S ^ k).range = (S ^ (k + 1)).range) :
    ∀ m : ℕ, (S ^ (k + m)).range = (S ^ k).range := by
  intro m
  induction m with
  | zero => simp only [Nat.add_zero]
  | succ m ih =>
    have step (j : ℕ) : (S ^ (j + 1)).range = ((S ^ j).range).map S :=
      S.iterateRange_succ
    calc
      (S ^ (k + (m + 1))).range = (S ^ ((k + m) + 1)).range := by rw [Nat.add_assoc]
      _ = ((S ^ (k + m)).range).map S := step _
      _ = ((S ^ k).range).map S := congrArg (fun V : Submodule K E => V.map S) ih
      _ = (S ^ (k + 1)).range := (step _).symm
      _ = (S ^ k).range := h.symm

/-- Stable kernel and range powers are complementary, without a dimension
assumption on the whole space. -/
theorem isCompl (S : Module.End K E) (n : ℕ)
    (hker : (S ^ (n + n)).ker = (S ^ n).ker)
    (hrange : (S ^ (n + n)).range = (S ^ n).range) :
    IsCompl (S ^ n).ker (S ^ n).range := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hr
    obtain ⟨y, hy⟩ := hr
    have hyker : y ∈ (S ^ (n + n)).ker := by
      change (S ^ (n + n)) y = 0
      rw [pow_add, Module.End.mul_eq_comp, LinearMap.comp_apply, hy]
      exact hx
    rw [hker] at hyker
    exact hy.symm.trans hyker
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hmem : (S ^ n) x ∈ (S ^ (n + n)).range := by
      rw [hrange]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hmem
    refine Submodule.mem_sup.mpr ⟨x - (S ^ n) y, ?_, (S ^ n) y, ⟨y, rfl⟩, by simp⟩
    change (S ^ n) (x - (S ^ n) y) = 0
    rw [map_sub, ← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← pow_add, hy, sub_self]

end LeanShared.StableKernelRange
