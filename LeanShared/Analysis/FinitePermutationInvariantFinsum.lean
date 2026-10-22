module

public import LeanShared.Analysis.FinitePermutationPrincipalMinors
public import Mathlib.Algebra.BigOperators.Finprod

/-! The finite signed permutation cancellation, indexed directly by the
nonempty invariant subsets.  This form accepts the actual periodic-walk
bijection without an arbitrary finite enumeration of symbolic paths.
-/

public noncomputable section
namespace LeanShared.FinitePermutationMinorCancellation
open Finset Set
variable {F : Type*} [Fintype F] [DecidableEq F] [Nonempty F]

theorem finsum_nonempty_invariant_signed_sum (P : Equiv.Perm F) :
    (∑ᶠ s : {s : Finset F // s.Nonempty ∧ ∀ p, P p ∈ s ↔ p ∈ s},
      -((-1 : ℚ) ^ s.val.card * (Equiv.Perm.sign (P.subtypePerm s.property.2) : ℚ))) = 1 := by
  classical
  let good := (Finset.univ : Finset (Finset F)).filter
    (fun s => s.Nonempty ∧ ∀ p, P p ∈ s ↔ p ∈ s)
  let weight := fun s : Finset F => -((-1 : ℚ) ^ s.card * invariantSubsetSign P s)
  calc
    _ = ∑ s : {s : Finset F // s.Nonempty ∧ ∀ p, P p ∈ s ↔ p ∈ s}, weight s.val := by
      rw [finsum_eq_sum_of_fintype]
      apply Finset.sum_congr rfl
      intro s _
      simp only [weight, invariantSubsetSign, dite_eq_left s.property.2]
    _ = ∑ s ∈ good, weight s :=
      (Finset.sum_subtype good (fun _ => by simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]) weight).symm
    _ = ∑ s ∈ (Finset.univ : Finset (Finset F)).erase ∅, weight s := by
      apply Finset.sum_subset
      · intro s member
        have nonempty := (Finset.mem_filter.mp member).2.1
        exact Finset.mem_erase.mpr ⟨nonempty.ne_empty, Finset.mem_univ s⟩
      · intro s member outside
        have nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp member).1
        have notInvariant : ¬ ∀ p, P p ∈ s ↔ p ∈ s := by
          intro invariant
          exact outside (Finset.mem_filter.mpr ⟨Finset.mem_univ s, nonempty, invariant⟩)
        simp only [weight, invariantSubsetSign, dite_eq_right notInvariant, mul_zero, neg_zero]
    _ = 1 := nonempty_invariant_signed_sum P

end LeanShared.FinitePermutationMinorCancellation
