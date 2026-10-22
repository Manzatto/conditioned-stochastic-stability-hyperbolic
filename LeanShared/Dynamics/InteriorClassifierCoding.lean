module

public import LeanShared.Dynamics.ClosedClassifierInteriorPaths

/-! Restrict the literal closed-classifier coding to nonempty-interior
symbols.  Whole-orbit interior itineraries lie in its image; compactness
and Baire density then prove that the restricted coding is still onto.
No classifier-origin packet is fabricated for the smaller alphabet.
-/

public noncomputable section
namespace LeanShared.FiniteClosedRefinement
open Set Function BilateralShadowingCoding MarkovFinitePathRealization
open scoped Topology
variable {X I : Type*} [MetricSpace X] [Fintype I]

instance interiorSymbolTopology (classifiers : I → Set X) : TopologicalSpace (InteriorSymbol classifiers) :=
  inferInstanceAs (TopologicalSpace {status : I → Bool // (interior (atom classifiers status)).Nonempty})

instance interiorSymbolDiscrete (classifiers : I → Set X) : DiscreteTopology (InteriorSymbol classifiers) :=
  inferInstanceAs (DiscreteTopology {status : I → Bool // (interior (atom classifiers status)).Nonempty})

@[expose] def interiorPathInclusion (T : X ≃ₜ X) (classifiers : I → Set X)
    (a : Path (Transition T (interiorRectangles classifiers))) :
    Path (Transition T (atom classifiers)) :=
  ⟨fun k => (a.val k).val, fun k => a.property k⟩

omit [Fintype I] in
theorem interiorPathInclusion_continuous (T : X ≃ₜ X) (classifiers : I → Set X) :
    Continuous (interiorPathInclusion T classifiers) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  exact continuous_subtype_val.comp ((continuous_apply k).comp continuous_subtype_val)

omit [Fintype I] in
theorem interiorPathInclusion_injective (T : X ≃ₜ X) (classifiers : I → Set X) :
    Injective (interiorPathInclusion T classifiers) := by
  intro a b equal
  apply Subtype.ext
  funext k
  apply Subtype.ext
  exact congrArg (fun c : Path (Transition T (atom classifiers)) => c.val k) equal

omit [Fintype I] in
theorem interiorPathInclusion_shift (T : X ≃ₜ X) (classifiers : I → Set X)
    (a : Path (Transition T (interiorRectangles classifiers))) :
    interiorPathInclusion T classifiers (shift _ a) = shift _ (interiorPathInclusion T classifiers a) := rfl

@[expose] def interiorCode (T : X ≃ₜ X) (classifiers : I → Set X)
    (code : Path (Transition T (atom classifiers)) → X) :
    Path (Transition T (interiorRectangles classifiers)) → X :=
  code ∘ interiorPathInclusion T classifiers

omit [Fintype I] in
theorem interiorCode_continuous (T : X ≃ₜ X) (classifiers : I → Set X)
    (code : Path (Transition T (atom classifiers)) → X) (continuous : Continuous code) :
    Continuous (interiorCode T classifiers code) :=
  continuous.comp (interiorPathInclusion_continuous T classifiers)

variable [DecidableEq I]

theorem fullOrbitInteriors_in_coding_image (T : X ≃ₜ X) (classifiers : I → Set X)
    (code : Path (Transition T (atom classifiers)) → X)
    (properties : MarkovCodingProperties T (atom classifiers) code) :
    fullOrbitInteriors T classifiers ⊆ range (interiorCode T classifiers code) := by
  intro x inside
  obtain ⟨a, itinerary⟩ := fullOrbitInteriors_path T classifiers x inside
  obtain ⟨b, coded⟩ := properties.onto x
  refine ⟨a, ?_⟩
  change code (interiorPathInclusion T classifiers a) = x
  rw [← coded]
  apply (properties.geometry.1 _ _).mpr
  intro k
  refine ⟨(T ^ k) x, subset_closure (interior_subset (itinerary k)), ?_⟩
  have coordinate := closed_window_coordinate T (atom classifiers) b.val k.natAbs (code b)
    (properties.windows b k.natAbs) k (by omega) (by omega)
  simpa only [coded] using coordinate

theorem interiorCode_surjective [BaireSpace X] [CompactSpace X]
    (T : X ≃ₜ X) (classifiers : I → Set X) (closed : ∀ i, IsClosed (classifiers i))
    (code : Path (Transition T (atom classifiers)) → X)
    (properties : MarkovCodingProperties T (atom classifiers) code) :
    Surjective (interiorCode T classifiers code) := by
  have denseImage : Dense (range (interiorCode T classifiers code)) :=
    (fullOrbitInteriors_dense T classifiers closed).mono (fullOrbitInteriors_in_coding_image T classifiers code properties)
  have closedImage : IsClosed (range (interiorCode T classifiers code)) :=
    (isCompact_range (interiorCode_continuous T classifiers code properties.continuous)).isClosed
  have full : range (interiorCode T classifiers code) = univ := by
    rw [← closedImage.closure_eq]
    exact denseImage.closure_eq
  exact range_eq_univ.mp full

end LeanShared.FiniteClosedRefinement
