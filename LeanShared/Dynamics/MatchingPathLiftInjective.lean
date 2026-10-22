module

public import LeanShared.Dynamics.SubsetMatchingPathLift

/-! The canonical bilateral tuple lift determines the entire matching
edge path, including its matching permutations.  This is the needed
finite-fiber injection for the actual signed correction coding.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [DecidableEq A] {R E : A → A → Prop} {k : ℕ}

omit [DecidableEq A] in
theorem subsetSymbol_range (s : FiberSubset E k) (x : A) :
    x ∈ s.val ↔ ∃ i, subsetSymbol s i = x := by
  constructor
  · intro inside
    refine ⟨(subsetEnumeration s).symm ⟨x, inside⟩, ?_⟩
    exact congrArg Subtype.val ((subsetEnumeration s).apply_symm_apply ⟨x, inside⟩)
  · rintro ⟨i, rfl⟩
    exact (subsetEnumeration s i).property

omit [DecidableEq A] in
theorem liftMatchingPath_injective :
    Injective (liftMatchingPath : Path (SubsetMatchingEdgeTransition R E k) → Path (FiberTupleTransition R E k)) := by
  intro a b equal
  have tuples (n : ℤ) (i : Fin k) : matchingPathTuple a n i = matchingPathTuple b n i :=
    congrArg (fun p : Path (FiberTupleTransition R E k) => p.val n i) equal
  have sources (n : ℤ) : (a.val n).val.1 = (b.val n).val.1 := by
    apply Subtype.ext
    ext x
    constructor
    · intro inside
      obtain ⟨i, symbol⟩ := (subsetSymbol_range (a.val n).val.1 x).mp inside
      apply (subsetSymbol_range (b.val n).val.1 x).mpr
      refine ⟨indexTransport (matchingPathPermutation b) n
        ((indexTransport (matchingPathPermutation a) n).symm i), ?_⟩
      have h := tuples n ((indexTransport (matchingPathPermutation a) n).symm i)
      change subsetSymbol (a.val n).val.1 _ = subsetSymbol (b.val n).val.1 _ at h
      rw [Equiv.apply_symm_apply] at h
      exact h.symm.trans symbol
    · intro inside
      obtain ⟨i, symbol⟩ := (subsetSymbol_range (b.val n).val.1 x).mp inside
      apply (subsetSymbol_range (a.val n).val.1 x).mpr
      refine ⟨indexTransport (matchingPathPermutation a) n
        ((indexTransport (matchingPathPermutation b) n).symm i), ?_⟩
      have h := tuples n ((indexTransport (matchingPathPermutation b) n).symm i)
      change subsetSymbol (a.val n).val.1 _ = subsetSymbol (b.val n).val.1 _ at h
      rw [Equiv.apply_symm_apply] at h
      exact h.trans symbol
  have transport (n : ℤ) : indexTransport (matchingPathPermutation a) n = indexTransport (matchingPathPermutation b) n := by
    apply Equiv.ext
    intro i
    apply subsetSymbol_injective (a.val n).val.1
    have h := tuples n i
    change subsetSymbol (a.val n).val.1 _ = subsetSymbol (b.val n).val.1 _ at h
    rw [← sources n] at h
    exact h
  have permutations (n : ℤ) : matchingPathPermutation a n = matchingPathPermutation b n := by
    have steps := (indexTransport_step (matchingPathPermutation a) n).symm.trans
      ((transport (n + 1)).trans (indexTransport_step (matchingPathPermutation b) n))
    rw [transport n] at steps
    have inverses : (matchingPathPermutation a n).symm = (matchingPathPermutation b n).symm := by
      apply Equiv.ext
      intro i
      have atIndex := congrArg (fun p : Equiv.Perm (Fin k) =>
        p ((indexTransport (matchingPathPermutation b) n).symm i)) steps
      simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using atIndex
    have h := congrArg (fun p : Equiv.Perm (Fin k) => p.symm) inverses
    simpa only [Equiv.symm_symm] using h
  apply Subtype.ext
  funext n
  apply Subtype.ext
  apply Prod.ext (sources n)
  apply Prod.ext
  · exact (a.property n).trans ((sources (n + 1)).trans (b.property n).symm)
  · exact permutations n

end LeanShared.BilateralShadowingCoding
