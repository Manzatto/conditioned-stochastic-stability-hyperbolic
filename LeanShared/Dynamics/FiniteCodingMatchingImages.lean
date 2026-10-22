module

public import LeanShared.Dynamics.FiniteCodingGeometry
public import LeanShared.Dynamics.SignedMatchingBoundaryImage

/-! Compact invariant higher matching images for the SAME finite coding
geometry as the primitive main graph.  The common boundary is the actual
boundary already produced from the retained classifier origin.
-/

public noncomputable section
namespace LeanShared.FiniteCodingManning
open Set Function BilateralShadowingCoding MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A]

theorem higher_matching_image_boundary (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (B : Set X)
    (boundary : ∀ a b, code a = code b → a.val 0 ≠ b.val 0 → code a ∈ B) (k : ℕ) :
    Set.range (matchingCode T rectangles code (k + 1)) ⊆ B := by
  rintro x ⟨a, rfl⟩
  have samePoint := tuple_coordinates_code_eq T rectangles code properties.geometry
    (liftMatchingPath a) (0 : Fin (k + 2)) 1
  apply boundary _ _ samePoint
  intro sameSymbol
  have injective := (matchingPathTuple_admissible a 0).2.2.2.1
  have indices : (0 : Fin (k + 2)) = 1 := injective sameSymbol
  have impossible := congrArg Fin.val indices
  norm_num at impossible

theorem matching_image_invariant (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code) (k : ℕ) :
    T '' Set.range (matchingCode T rectangles code k) = Set.range (matchingCode T rectangles code k) := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨shift _ a, matchingCode_intertwines T rectangles code properties.geometry properties.intertwines k a⟩
  · rintro ⟨a, rfl⟩
    let b := (shift (SubsetMatchingEdgeTransition (Transition T rectangles) (Affiliated rectangles) (k + 1))).symm a
    refine ⟨matchingCode T rectangles code k b, ⟨b, rfl⟩, ?_⟩
    have identity := matchingCode_intertwines T rectangles code properties.geometry properties.intertwines k b
    simpa only [b, Homeomorph.apply_symm_apply] using identity.symm

theorem matching_image_compact (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code) (k : ℕ) :
    IsCompact (Set.range (matchingCode T rectangles code k)) :=
  isCompact_range (matchingCode_continuous T rectangles code properties.continuous k)

@[expose] def higherMatchingImage (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) : Set X :=
  ⋃ k : Fin (Fintype.card A), Set.range (matchingCode T rectangles code (k.val + 1))

theorem higherMatchingImage_compact (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code) :
    IsCompact (higherMatchingImage T rectangles code) :=
  isCompact_iUnion (fun k : Fin (Fintype.card A) => matching_image_compact T rectangles code properties (k.val + 1))

theorem higherMatchingImage_invariant (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code) :
    T '' higherMatchingImage T rectangles code = higherMatchingImage T rectangles code := by
  dsimp only [higherMatchingImage]
  rw [Set.image_iUnion]
  exact congrArg (fun f : Fin (Fintype.card A) → Set X => ⋃ k, f k)
    (funext (fun k => matching_image_invariant T rectangles code properties (k.val + 1)))

theorem higherMatchingImage_subset_boundary (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (B : Set X) (boundary : ∀ a b, code a = code b → a.val 0 ≠ b.val 0 → code a ∈ B) :
    higherMatchingImage T rectangles code ⊆ B := by
  intro x inside
  obtain ⟨k, member⟩ := mem_iUnion.mp inside
  exact higher_matching_image_boundary T rectangles code properties B boundary k.val member

theorem higherMatchingImage_proper [Nonempty X] (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (B : Set X) (emptyInterior : interior B = ∅)
    (boundary : ∀ a b, code a = code b → a.val 0 ≠ b.val 0 → code a ∈ B) :
    higherMatchingImage T rectangles code ≠ univ := by
  intro full
  have included := higherMatchingImage_subset_boundary T rectangles code properties B boundary
  rw [full] at included
  have fullB : B = univ := univ_subset_iff.mp included
  rw [fullB, interior_univ] at emptyInterior
  exact univ_nonempty.ne_empty emptyInterior

end LeanShared.FiniteCodingManning
