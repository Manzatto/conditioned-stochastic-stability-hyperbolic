module

public import LeanShared.Analysis.FinitePermutationMinorCancellation

/-! A principal minor of a permutation matrix vanishes unless its subset
is invariant.  On an invariant subset it is exactly the sign of the
restricted permutation.  Thus the proved signed-minor cancellation has
the literal invariant-subset interpretation needed for periodic fibers.
-/

public noncomputable section
namespace LeanShared.FinitePermutationMinorCancellation
open Matrix Finset Set
variable {F 𝕜 : Type*} [Fintype F] [DecidableEq F] [Field 𝕜]

omit [Fintype F] [DecidableEq F] in
theorem permutation_invariant_of_mapsTo (P : Equiv.Perm F) (s : Finset F)
    (maps : ∀ i ∈ s, P i ∈ s) : ∀ i, P i ∈ s ↔ i ∈ s := by
  have bijective := (s.finite_toSet.injOn_iff_bijOn_of_mapsTo maps).mp P.injective.injOn
  intro i
  constructor
  · intro inside
    obtain ⟨j, hj, equal⟩ := bijective.surjOn inside
    exact (P.injective equal) ▸ hj
  · exact maps i

omit [Fintype F] in
theorem permutation_minor_zero (P : Equiv.Perm F) (s : Finset F)
    (notInvariant : ¬ ∀ i, P i ∈ s ↔ i ∈ s) :
    ((P.permMatrix 𝕜).submatrix (Subtype.val : s → F) Subtype.val).det = 0 := by
  have leaves : ∃ i ∈ s, P i ∉ s := by
    by_contra! all
    exact notInvariant (permutation_invariant_of_mapsTo P s all)
  obtain ⟨i, inside, outside⟩ := leaves
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨i, inside⟩
  intro j
  have different : j.val ≠ P i := by
    intro equal
    exact outside (equal ▸ j.property)
  simp only [Matrix.submatrix_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_some, ite_eq_right (Ne.symm different)]

omit [Fintype F] in
theorem permutation_minor_sign (P : Equiv.Perm F) (s : Finset F)
    (invariant : ∀ i, P i ∈ s ↔ i ∈ s) :
    ((P.permMatrix 𝕜).submatrix (Subtype.val : s → F) Subtype.val).det =
      (Equiv.Perm.sign (P.subtypePerm invariant) : 𝕜) := by
  have matrixEqual : (P.permMatrix 𝕜).submatrix (Subtype.val : s → F) Subtype.val =
      (P.subtypePerm invariant).permMatrix 𝕜 := by
    ext i j
    simp only [Matrix.submatrix_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_some]
    congr 1
    apply propext
    constructor
    · intro equal
      apply Subtype.ext
      exact equal
    · intro equal
      exact congrArg (fun a : s => a.val) equal
  rw [matrixEqual, Matrix.det_permutation]

omit [Fintype F] in
@[expose] def invariantSubsetSign (P : Equiv.Perm F) (s : Finset F) : 𝕜 := by
  classical
  exact if h : ∀ i, P i ∈ s ↔ i ∈ s then (Equiv.Perm.sign (P.subtypePerm h) : 𝕜) else 0

theorem permutation_minor_eq_invariant_sign (P : Equiv.Perm F) (s : Finset F) :
    ((P.permMatrix 𝕜).submatrix (Subtype.val : s → F) Subtype.val).det =
      invariantSubsetSign P s := by
  classical
  by_cases invariant : ∀ i, P i ∈ s ↔ i ∈ s
  · simpa only [invariantSubsetSign, dite_eq_left invariant] using permutation_minor_sign P s invariant
  · simpa only [invariantSubsetSign, dite_eq_right invariant] using permutation_minor_zero P s invariant

theorem nonempty_invariant_signed_sum [Nonempty F] (P : Equiv.Perm F) :
    (∑ s ∈ (Finset.univ : Finset (Finset F)).erase ∅,
      -((-1 : 𝕜) ^ s.card * invariantSubsetSign P s)) = 1 := by
  simpa only [permutation_minor_eq_invariant_sign] using permutation_nonempty_signed_minors (𝕜 := 𝕜) P

end LeanShared.FinitePermutationMinorCancellation
