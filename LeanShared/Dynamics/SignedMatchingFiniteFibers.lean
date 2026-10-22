module

public import LeanShared.Dynamics.MatchingPathLiftInjective
public import LeanShared.Dynamics.SignedMatchingCoding
public import LeanShared.Dynamics.MarkovCodingProperties

/-! The literal signed matching coding has uniformly bounded finite
fibers.  Its canonical lift injects each fiber into a finite power of an
original coding fiber.  Matching permutations are retained, so this
argument also bounds multiple matching edges.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A]

theorem matchingCode_fiber_bound (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (k : ℕ) (x : X) :
    ((matchingCode T rectangles code k) ⁻¹' {x}).Finite ∧
      ((matchingCode T rectangles code k) ⁻¹' {x}).ncard ≤ ((Fintype.card A) ^ 2) ^ (k + 1) := by
  classical
  let originalFiber := code ⁻¹' {x}
  let correctionFiber := (matchingCode T rectangles code k) ⁻¹' {x}
  let : Finite originalFiber := Set.finite_coe_iff.mpr (properties.finiteFibers x)
  have inside (a : correctionFiber) (i : Fin (k + 1)) :
      tupleCoordinate (liftMatchingPath a.val) i ∈ originalFiber := by
    change code (tupleCoordinate (liftMatchingPath a.val) i) = x
    have samePoint := tuple_coordinates_code_eq T rectangles code properties.geometry (liftMatchingPath a.val) i 0
    exact samePoint.trans a.property
  let encode : correctionFiber → (Fin (k + 1) → originalFiber) :=
    fun a i => ⟨tupleCoordinate (liftMatchingPath a.val) i, inside a i⟩
  have injective : Injective encode := by
    intro a b equal
    apply Subtype.ext
    apply liftMatchingPath_injective
    apply Subtype.ext
    funext n i
    have paths := congrArg (fun f : Fin (k + 1) → originalFiber => (f i).val) equal
    exact congrArg (fun p : Path (Transition T rectangles) => p.val n) paths
  let : Finite correctionFiber := Finite.of_injective encode injective
  refine ⟨Set.finite_coe_iff.mp inferInstance, ?_⟩
  have count := Nat.card_le_card_of_injective encode injective
  have estimate : correctionFiber.ncard ≤ originalFiber.ncard ^ (k + 1) := by
    simpa only [Nat.card_fun, Nat.card_fin, Nat.card_coe_set_eq] using count
  exact estimate.trans (Nat.pow_le_pow_left (properties.fibers x).2 (k + 1))

end LeanShared.BilateralShadowingCoding
