module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Module.Complemented

/-! The restriction of an operator to its stabilized complementary range is
an actual bounded linear isomorphism. -/

public section
open ContinuousLinearMap Submodule
namespace LeanShared.StableRangeInverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The stable-range block of a Fitting decomposition is continuously invertible.
Neither a bounded inverse nor a resolvent hypothesis is an input. -/
theorem exists_equiv (S : E →L[ℂ] E) (n : ℕ)
    (hcompl : IsTopCompl (S ^ n).ker (S ^ n).range)
    (hker : (S ^ (n + 1)).ker = (S ^ n).ker)
    (hrange : (S ^ (n + 1)).range = (S ^ n).range) :
    ∃ e : (S ^ n).range ≃L[ℂ] (S ^ n).range, ∀ x, (e x).val = S x.val := by
  let V := (S ^ n).range
  let : CompleteSpace V := hcompl.isClosed'.isComplete.completeSpace_coe
  have invariant : ∀ x ∈ V, S x ∈ V := by
    intro x hx
    obtain ⟨v, hv⟩ := hx
    change (S ^ n) v = x at hv
    refine ⟨S v, ?_⟩
    change (S ^ n) (S v) = S x
    rw [← mul_apply_eq_comp, ← pow_succ, pow_succ', mul_apply_eq_comp, hv]
  let SJ : V →L[ℂ] V := S.restrict invariant
  have hinj : Function.Injective SJ := by
    change Function.Injective (SJ : V →ₗ[ℂ] V)
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx0 : S x.val = 0 := congrArg Subtype.val hx
    have hk : x.val ∈ (S ^ n).ker := by
      rw [← hker]
      change (S ^ (n + 1)) x.val = 0
      rw [pow_succ, mul_apply_eq_comp, hx0, map_zero]
    have hz : x.val = 0 := (Submodule.disjoint_def.mp hcompl.isCompl.disjoint) x.val hk x.property
    exact Subtype.ext hz
  have hsurj : Function.Surjective SJ := by
    intro y
    have hy : y.val ∈ (S ^ (n + 1)).range := by rw [hrange]; exact y.property
    obtain ⟨v, hv⟩ := hy
    refine ⟨⟨(S ^ n) v, ⟨v, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change S ((S ^ n) v) = y.val
    change (S ^ (n + 1)) v = y.val at hv
    rw [pow_succ'] at hv
    exact hv
  let e := ContinuousLinearEquiv.ofBijective SJ
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨e, fun _ => rfl⟩

end LeanShared.StableRangeInverse
