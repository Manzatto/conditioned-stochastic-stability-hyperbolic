module

public import LeanShared.Dynamics.MatchingFiberSubsets
public import LeanShared.Dynamics.TupleMatchingCodingCompatibility

/-! Over an actual periodic base point, projecting a finite family of
original lifts to the matching graph preserves the EXACT extracted
subset.  Original periodic fiber symbols separate points, so canonical
reordering cannot lose or replace a lift.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A]

theorem matchingFiberSubset_tuple_projection (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code)
    (x : X) [DecidableEq (code ⁻¹' {x})] (period : ℕ) (positive : 0 < period)
    (fixed : (T : X → X)^[period] x = x) (k : ℕ)
    (a : Path (FiberTupleTransition (Transition T rectangles) (Affiliated rectangles) (k + 1)))
    (lifts : Fin (k + 1) → code ⁻¹' {x})
    (coordinates : ∀ i, tupleCoordinate a i = (lifts i).val)
    (inside : matchingCode T rectangles code k (tupleToMatchingPath a) = x) :
    matchingFiberSubset T rectangles code properties.geometry k x ⟨tupleToMatchingPath a, inside⟩ =
      Finset.univ.image lifts := by
  classical
  apply Finset.image_injective (properties.periodicSymbols x period positive fixed 0)
  rw [← matchingFiberSubset_source_labels T rectangles code properties.geometry k x ⟨tupleToMatchingPath a, inside⟩]
  change Finset.univ.image (a.val 0) = (Finset.univ.image lifts).image (fun p : code ⁻¹' {x} => p.val.val 0)
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact congrArg (fun p : Path (Transition T rectangles) => p.val 0) (coordinates i)

end LeanShared.BilateralShadowingCoding
