module

public import LeanShared.Dynamics.SignedMatchingFiniteFibers

/-! Canonically extract the finite set of original symbolic lifts from
an actual correction fiber.  Its cardinal is the matching order, and
over periodic base points this extraction is injective: the actual
original fiber is separated by time-zero labels.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A]

@[expose] def matchingFiberCoordinate (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code) (k : ℕ) (x : X)
    (a : (matchingCode T rectangles code k) ⁻¹' {x}) (i : Fin (k + 1)) : code ⁻¹' {x} :=
  ⟨tupleCoordinate (liftMatchingPath a.val) i,
    (tuple_coordinates_code_eq T rectangles code geometry (liftMatchingPath a.val) i 0).trans a.property⟩

@[expose] def matchingFiberSubset (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code) (k : ℕ) (x : X)
    (a : (matchingCode T rectangles code k) ⁻¹' {x}) : Finset (code ⁻¹' {x}) := by
  classical
  exact Finset.univ.image (matchingFiberCoordinate T rectangles code geometry k x a)

omit [TopologicalSpace A] [Fintype A] in
theorem matchingFiberCoordinate_injective (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code) (k : ℕ) (x : X)
    (a : (matchingCode T rectangles code k) ⁻¹' {x}) :
    Injective (matchingFiberCoordinate T rectangles code geometry k x a) := by
  intro i j equal
  apply (matchingPathTuple_admissible a.val 0).2.2.2.1
  exact congrArg (fun p : code ⁻¹' {x} => p.val.val 0) equal

omit [TopologicalSpace A] [Fintype A] in
theorem matchingFiberSubset_card (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code) (k : ℕ) (x : X)
    (a : (matchingCode T rectangles code k) ⁻¹' {x}) :
    (matchingFiberSubset T rectangles code geometry k x a).card = k + 1 := by
  classical
  simpa only [matchingFiberSubset, Finset.card_univ, Fintype.card_fin] using
    Finset.card_image_of_injective Finset.univ
      (matchingFiberCoordinate_injective T rectangles code geometry k x a)

omit [TopologicalSpace A] [Fintype A] in
theorem matchingFiberSubset_source_labels [DecidableEq A] (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code) (k : ℕ) (x : X)
    (a : (matchingCode T rectangles code k) ⁻¹' {x}) :
    (a.val.val 0).val.1.val = (matchingFiberSubset T rectangles code geometry k x a).image
      (fun p : code ⁻¹' {x} => p.val.val 0) := by
  classical
  ext label
  constructor
  · intro inside
    obtain ⟨i, equal⟩ := (subsetSymbol_range (a.val.val 0).val.1 label).mp inside
    refine Finset.mem_image.mpr ⟨matchingFiberCoordinate T rectangles code geometry k x a i,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    exact equal
  · intro inside
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp inside
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (subsetEnumeration (a.val.val 0).val.1 i).property

theorem matchingFiberSubset_injective (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (k : ℕ) (x : X)
    (period : ℕ) (positive : 0 < period) (fixed : (T : X → X)^[period] x = x) :
    Injective (matchingFiberSubset T rectangles code properties.geometry k x) := by
  classical
  intro a b equal
  have sources : (a.val.val 0).val.1 = (b.val.val 0).val.1 := by
    apply Subtype.ext
    rw [matchingFiberSubset_source_labels T rectangles code properties.geometry k x a,
      matchingFiberSubset_source_labels T rectangles code properties.geometry k x b, equal]
  have coordinates (i : Fin (k + 1)) :
      matchingFiberCoordinate T rectangles code properties.geometry k x a i =
        matchingFiberCoordinate T rectangles code properties.geometry k x b i := by
    apply properties.periodicSymbols x period positive fixed 0
    change subsetSymbol (a.val.val 0).val.1 i = subsetSymbol (b.val.val 0).val.1 i
    rw [sources]
  apply Subtype.ext
  apply liftMatchingPath_injective
  apply Subtype.ext
  funext n i
  exact congrArg (fun p : code ⁻¹' {x} => p.val.val n) (coordinates i)

end LeanShared.BilateralShadowingCoding
