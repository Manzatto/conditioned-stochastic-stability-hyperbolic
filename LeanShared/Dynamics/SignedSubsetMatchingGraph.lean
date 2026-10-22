module

public import LeanShared.Dynamics.SymbolicFiberTuples
public import LeanShared.Analysis.FinitePermutationPrincipalMinors
public import Mathlib.Data.Fintype.EquivFin

/-! The finite local graph for signed unordered fiber corrections.
Vertices are actual affiliated k-element label subsets.  Each edge is an
allowed matching bijection; its sign and the signed adjacency matrix are
literal finite constructions.  Multiple matching edges are retained.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Matrix
variable {A : Type*} [DecidableEq A]

@[expose] def FiberSubset (E : A → A → Prop) (k : ℕ) : Type _ :=
  {s : Finset A // s.card = k ∧ ∀ i ∈ s, ∀ j ∈ s, E i j}

instance [Fintype A] (E : A → A → Prop) (k : ℕ) : Finite (FiberSubset E k) :=
  inferInstanceAs (Finite {s : Finset A // s.card = k ∧ ∀ i ∈ s, ∀ j ∈ s, E i j})

instance [Fintype A] (E : A → A → Prop) (k : ℕ) : Fintype (FiberSubset E k) := Fintype.ofFinite _

@[expose] def subsetEnumeration {E : A → A → Prop} {k : ℕ} (s : FiberSubset E k) : Fin k ≃ s.val :=
  (s.val.equivFinOfCardEq s.property.1).symm

@[expose] def subsetSymbol {E : A → A → Prop} {k : ℕ} (s : FiberSubset E k) (i : Fin k) : A :=
  (subsetEnumeration s i).val

omit [DecidableEq A] in
theorem subsetSymbol_injective {E : A → A → Prop} {k : ℕ} (s : FiberSubset E k) :
    Injective (subsetSymbol s) :=
  Subtype.val_injective.comp (subsetEnumeration s).injective

omit [DecidableEq A] in
theorem subsetSymbol_related {E : A → A → Prop} {k : ℕ} (s : FiberSubset E k) (i j : Fin k) :
    E (subsetSymbol s i) (subsetSymbol s j) :=
  s.property.2 _ (subsetEnumeration s i).property _ (subsetEnumeration s j).property

/-- Target-to-source index matching, the convention in the determinant
expansion.  The forward matching is its inverse and has the same sign. -/
@[expose] def IsSubsetMatching (R : A → A → Prop) {E : A → A → Prop} {k : ℕ}
    (s t : FiberSubset E k) (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ i, R (subsetSymbol s (σ i)) (subsetSymbol t i)

@[expose] def signedSubsetAdjacency (R : A → A → Prop) {E : A → A → Prop} {k : ℕ}
    (s t : FiberSubset E k) : ℤ := by
  classical
  exact ∑ σ : Equiv.Perm (Fin k), if IsSubsetMatching R s t σ then (Equiv.Perm.sign σ : ℤ) else 0

@[expose] def subsetTransitionMatrix (R : A → A → Prop) {E : A → A → Prop} {k : ℕ}
    (s t : FiberSubset E k) : Matrix (Fin k) (Fin k) ℤ := by
  classical
  exact fun i j => if R (subsetSymbol s i) (subsetSymbol t j) then 1 else 0

omit [DecidableEq A] in
theorem signedSubsetAdjacency_eq_det (R : A → A → Prop) {E : A → A → Prop} {k : ℕ}
    (s t : FiberSubset E k) :
    signedSubsetAdjacency R s t = (subsetTransitionMatrix R s t).det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  by_cases allowed : IsSubsetMatching R s t σ
  · simp only [ite_eq_left allowed]
    have entries (i : Fin k) : subsetTransitionMatrix R s t (σ i) i = 1 :=
      ite_eq_left (allowed i)
    simp only [entries, Finset.prod_const_one, mul_one, Int.cast_id]
  · obtain ⟨i, forbidden⟩ := not_forall.mp allowed
    have zeroProduct : (∏ j : Fin k, subsetTransitionMatrix R s t (σ j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right forbidden)
    simp only [ite_eq_right allowed, zeroProduct, mul_zero]

@[expose] def SubsetMatchingEdge (R E : A → A → Prop) (k : ℕ) : Type _ :=
  {p : FiberSubset E k × FiberSubset E k × Equiv.Perm (Fin k) //
    IsSubsetMatching R p.1 p.2.1 p.2.2}

instance [Fintype A] (R E : A → A → Prop) (k : ℕ) : Finite (SubsetMatchingEdge R E k) :=
  inferInstanceAs (Finite {p : FiberSubset E k × FiberSubset E k × Equiv.Perm (Fin k) //
    IsSubsetMatching R p.1 p.2.1 p.2.2})

instance [Fintype A] (R E : A → A → Prop) (k : ℕ) : Fintype (SubsetMatchingEdge R E k) := Fintype.ofFinite _

@[expose] def SubsetMatchingEdgeTransition (R E : A → A → Prop) (k : ℕ)
    (e f : SubsetMatchingEdge R E k) : Prop := e.val.2.1 = f.val.1

end LeanShared.BilateralShadowingCoding
