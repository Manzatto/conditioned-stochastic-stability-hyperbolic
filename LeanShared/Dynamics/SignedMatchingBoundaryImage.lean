module

public import LeanShared.Dynamics.SignedMatchingCoding
public import LeanShared.Dynamics.MarkovCodingProperties

/-! Higher matching corrections code into the actual closed classifier
boundary.  Their images are compact and invariant; the retained raw
classifier origin proves empty interior, and hence properness on every
nonempty core.  No pressure gap is assumed in this result.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
open scoped Topology
variable {A X : Type*} [MetricSpace X] [BaireSpace X] [DecidableEq A] [TopologicalSpace A] [Fintype A]

omit [DecidableEq A] in
theorem higher_matching_image_boundary (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (k : ℕ) :
    ∃ boundary : Set X, IsClosed boundary ∧ interior boundary = ∅ ∧
      Set.range (matchingCode T rectangles code (k + 1)) ⊆ boundary := by
  obtain ⟨boundary, closed, emptyInterior, contains⟩ := properties.symbolBoundary
  refine ⟨boundary, closed, emptyInterior, ?_⟩
  rintro x ⟨a, rfl⟩
  have samePoint := tuple_coordinates_code_eq T rectangles code properties.geometry
    (liftMatchingPath a) (0 : Fin (k + 2)) 1
  apply contains _ _ samePoint
  intro sameSymbol
  have injective := (matchingPathTuple_admissible a 0).2.2.2.1
  have indices : (0 : Fin (k + 2)) = 1 := injective sameSymbol
  have impossible := congrArg Fin.val indices
  norm_num at impossible

omit [DecidableEq A] in
theorem higher_matching_image_empty_interior (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (k : ℕ) :
    interior (Set.range (matchingCode T rectangles code (k + 1))) = ∅ := by
  obtain ⟨_, _, emptyInterior, contains⟩ := higher_matching_image_boundary T rectangles code properties k
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x inside
  have estimate := interior_mono contains inside
  rw [emptyInterior] at estimate
  exact estimate

omit [BaireSpace X] [DecidableEq A] in
theorem matching_image_invariant (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (k : ℕ) :
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

omit [BaireSpace X] [DecidableEq A] in
theorem matching_image_compact (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (k : ℕ) :
    IsCompact (Set.range (matchingCode T rectangles code k)) :=
  isCompact_range (matchingCode_continuous T rectangles code properties.continuous k)

omit [DecidableEq A] in
theorem higher_matching_image_proper [Nonempty X] (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (k : ℕ) :
    Set.range (matchingCode T rectangles code (k + 1)) ≠ Set.univ := by
  intro full
  have emptyInterior := higher_matching_image_empty_interior T rectangles code properties k
  rw [full, interior_univ] at emptyInterior
  exact Set.univ_nonempty.ne_empty emptyInterior

end LeanShared.BilateralShadowingCoding
