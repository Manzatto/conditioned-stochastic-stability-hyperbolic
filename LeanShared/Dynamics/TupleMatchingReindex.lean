module

public import LeanShared.Dynamics.TupleToSubsetMatchingPath

/-! Reordering an ordered fiber tuple changes neither its unordered
vertex nor its exact matching edge.  This identifies genuine permutation
monodromy with periodic paths of the signed matching graph.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Function
variable {A : Type*} [DecidableEq A] {R E : A → A → Prop} {k : ℕ}

theorem tupleVertex_reindex (u : Fin k → A) (hu : Injective u)
    (eu : ∀ i j, E (u i) (u j)) (q : Equiv.Perm (Fin k)) :
    tupleVertex (u ∘ q) (hu.comp q.injective) (fun i j => eu (q i) (q j)) = tupleVertex u hu eu := by
  apply Subtype.ext
  ext x
  change x ∈ Finset.univ.image (u ∘ q) ↔ x ∈ Finset.univ.image u
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨q i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨q.symm i, congrArg u (q.apply_symm_apply i)⟩

theorem tupleOrdering_reindex (u : Fin k → A) (hu : Injective u)
    (eu : ∀ i j, E (u i) (u j)) (q : Equiv.Perm (Fin k)) :
    tupleOrdering (u ∘ q) (hu.comp q.injective) (fun i j => eu (q i) (q j)) =
      (tupleOrdering u hu eu).trans q.symm := by
  apply Equiv.ext
  intro i
  have first := tupleOrdering_symbol (u ∘ q) (hu.comp q.injective) (fun i j => eu (q i) (q j)) i
  rw [tupleVertex_reindex u hu eu q] at first
  have second := tupleOrdering_symbol u hu eu i
  have equal : q (tupleOrdering (u ∘ q) (hu.comp q.injective) (fun i j => eu (q i) (q j)) i) =
      tupleOrdering u hu eu i := hu (first.symm.trans second)
  exact q.eq_symm_apply.mpr equal

theorem tupleMatchingEdge_reindex (u v : Fin k → A) (hu : Injective u) (hv : Injective v)
    (eu : ∀ i j, E (u i) (u j)) (ev : ∀ i j, E (v i) (v j))
    (allowed : ∀ i, R (u i) (v i)) (q : Equiv.Perm (Fin k)) :
    tupleMatchingEdge (u ∘ q) (v ∘ q) (hu.comp q.injective) (hv.comp q.injective)
      (fun i j => eu (q i) (q j)) (fun i j => ev (q i) (q j)) (fun i => allowed (q i)) =
      tupleMatchingEdge u v hu hv eu ev allowed := by
  apply Subtype.ext
  apply Prod.ext (tupleVertex_reindex u hu eu q)
  apply Prod.ext (tupleVertex_reindex v hv ev q)
  change (tupleOrdering (v ∘ q) (hv.comp q.injective) (fun i j => ev (q i) (q j))).trans
    (tupleOrdering (u ∘ q) (hu.comp q.injective) (fun i j => eu (q i) (q j))).symm =
    (tupleOrdering v hv ev).trans (tupleOrdering u hu eu).symm
  rw [tupleOrdering_reindex v hv ev q, tupleOrdering_reindex u hu eu q]
  apply Equiv.ext
  intro i
  simp only [Equiv.symm_trans, Equiv.symm_symm, Equiv.trans_apply, Equiv.apply_symm_apply]

end LeanShared.BilateralShadowingCoding
