module

public import LeanShared.Dynamics.SignedMatchingCoding
public import LeanShared.Dynamics.TupleToSubsetMatchingPath

/-! The actual coding of an unordered matching projection is exactly
the original code of each tuple coordinate.  This retains literal
potential and periodic-energy identities across the correction graph.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [DecidableEq A] [TopologicalSpace A]

omit [TopologicalSpace A] in
theorem matchingCode_tuple_projection (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code) (k : ℕ)
    (a : Path (FiberTupleTransition (Transition T rectangles) (Affiliated rectangles) (k + 1)))
    (i : Fin (k + 1)) :
    matchingCode T rectangles code k (tupleToMatchingPath a) = code (tupleCoordinate a i) := by
  apply (geometry.1 _ _).mpr
  intro n
  change Affiliated rectangles
    (subsetSymbol (tupleVertex (a.val n) (a.property n).2.2.2.1 (a.property n).2.1)
      (indexTransport (matchingPathPermutation (tupleToMatchingPath a)) n 0)) (a.val n i)
  rw [tupleOrdering_symbol]
  exact (a.property n).2.1 _ i

end LeanShared.BilateralShadowingCoding
