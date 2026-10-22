module

public import LeanShared.Dynamics.BilateralPermutationCocycle

/-! Every path in the literal signed matching-edge graph lifts to a
separated ordered tuple path.  Bilateral index transport follows the
actual matching bijections in both directions; source/target consistency
supplies genuine original graph edges.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Function
variable {A : Type*} [DecidableEq A] {R E : A → A → Prop} {k : ℕ}

@[expose] def matchingPathPermutation (a : Path (SubsetMatchingEdgeTransition R E k))
    (n : ℤ) : Equiv.Perm (Fin k) := (a.val n).val.2.2

@[expose] def matchingPathTuple (a : Path (SubsetMatchingEdgeTransition R E k))
    (n : ℤ) (i : Fin k) : A :=
  subsetSymbol (a.val n).val.1 (indexTransport (matchingPathPermutation a) n i)

omit [DecidableEq A] in
theorem matchingPathTuple_admissible (a : Path (SubsetMatchingEdgeTransition R E k)) (n : ℤ) :
    FiberTupleTransition R E k (matchingPathTuple a n) (matchingPathTuple a (n + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    let π := matchingPathPermutation a n
    let q := indexTransport (matchingPathPermutation a) n
    have allowed := (a.val n).property (π.symm (q i))
    have endpoints := a.property n
    change (a.val n).val.2.1 = (a.val (n + 1)).val.1 at endpoints
    change R (subsetSymbol (a.val n).val.1 (π (π.symm (q i))))
      (subsetSymbol (a.val n).val.2.1 (π.symm (q i))) at allowed
    rw [Equiv.apply_symm_apply, endpoints] at allowed
    change R (subsetSymbol (a.val n).val.1 (q i))
      (subsetSymbol (a.val (n + 1)).val.1 (indexTransport (matchingPathPermutation a) (n + 1) i))
    rw [indexTransport_step]
    exact allowed
  · intro i j
    exact subsetSymbol_related _ _ _
  · intro i j
    exact subsetSymbol_related _ _ _
  · exact (subsetSymbol_injective _).comp (indexTransport (matchingPathPermutation a) n).injective
  · exact (subsetSymbol_injective _).comp (indexTransport (matchingPathPermutation a) (n + 1)).injective

@[expose] def liftMatchingPath (a : Path (SubsetMatchingEdgeTransition R E k)) :
    Path (FiberTupleTransition R E k) :=
  ⟨matchingPathTuple a, matchingPathTuple_admissible a⟩

omit [DecidableEq A] in
theorem liftMatchingPath_symbol (a : Path (SubsetMatchingEdgeTransition R E k)) (n : ℤ) (i : Fin k) :
    (tupleCoordinate (liftMatchingPath a) i).val n =
      subsetSymbol (a.val n).val.1 (indexTransport (matchingPathPermutation a) n i) := rfl

end LeanShared.BilateralShadowingCoding
