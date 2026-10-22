module

public import LeanShared.Dynamics.InteriorClassifierCoding
public import LeanShared.Dynamics.MixingClassifierInteriorGraph
public import LeanShared.Dynamics.SymbolicExponentialVariation

/-! The actual retained classifier origin supplies a literal embedding of the full-interior graph
into any enumerated original coding graph. The restricted map is still continuous, onto and
finite-to-one. This works directly with the packet, without asserting a spurious full Boolean
enumeration for the pruned alphabet. -/

public noncomputable section
namespace LeanShared.FiniteClosedRefinement
open Set Function BilateralShadowingCoding MarkovFinitePathRealization
open scoped Topology
variable {X J : Type*} [MetricSpace X] [TopologicalSpace J] [DiscreteTopology J] [Fintype J]
  {d : ℕ} (T : X ≃ₜ X) (C : Fin d → Set X) (rectangles : J → Set X)
  (statuses : J ≃ (Fin d → Bool)) (law : ∀ j, rectangles j = atom C (statuses j))

@[expose] def interiorReindexPath
    (a : Path (Transition T (interiorRectangles C))) : Path (Transition T rectangles) :=
  ⟨fun k => statuses.symm (a.val k).val, fun k => by
    change ∃ x ∈ rectangles (statuses.symm (a.val k).val), T x ∈ rectangles (statuses.symm (a.val (k + 1)).val)
    simpa only [law, Equiv.apply_symm_apply, Transition, interiorRectangles] using a.property k⟩

omit [DiscreteTopology J] [Fintype J] in
theorem interiorReindexPath_continuous : Continuous (interiorReindexPath T C rectangles statuses law) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  have label : Continuous (fun j : InteriorSymbol C => statuses.symm j.val) := continuous_of_discreteTopology
  exact label.comp ((continuous_apply k).comp continuous_subtype_val)

omit [TopologicalSpace J] [DiscreteTopology J] [Fintype J] in
theorem interiorReindexPath_injective : Injective (interiorReindexPath T C rectangles statuses law) := by
  intro a b equal
  apply Subtype.ext
  funext k
  apply Subtype.ext
  apply statuses.symm.injective
  exact congrArg (fun c : Path (Transition T rectangles) => c.val k) equal

@[expose] def reindexedInteriorCode (code : Path (Transition T rectangles) → X) :
    Path (Transition T (interiorRectangles C)) → X :=
  code ∘ interiorReindexPath T C rectangles statuses law

omit [DiscreteTopology J] [Fintype J] in
theorem reindexedInteriorCode_continuous (code : Path (Transition T rectangles) → X)
    (continuous : Continuous code) : Continuous (reindexedInteriorCode T C rectangles statuses law code) :=
  continuous.comp (interiorReindexPath_continuous T C rectangles statuses law)

omit [DiscreteTopology J] in
theorem reindexedInteriorCode_surjective [BaireSpace X] [CompactSpace X]
    (closed : ∀ i, IsClosed (C i)) (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) :
    Surjective (reindexedInteriorCode T C rectangles statuses law code) := by
  have goodImage : fullOrbitInteriors T C ⊆ range (reindexedInteriorCode T C rectangles statuses law code) := by
    intro x inside
    obtain ⟨a, itinerary⟩ := fullOrbitInteriors_path T C x inside
    obtain ⟨b, coded⟩ := properties.onto x
    refine ⟨a, ?_⟩
    change code (interiorReindexPath T C rectangles statuses law a) = x
    rw [← coded]
    apply (properties.geometry.1 _ _).mpr
    intro k
    refine ⟨(T ^ k) x, ?_, ?_⟩
    · change (T ^ k) x ∈ closure (rectangles (statuses.symm (a.val k).val))
      rw [law, Equiv.apply_symm_apply]
      exact subset_closure (interior_subset (itinerary k))
    · have coordinate := closed_window_coordinate T rectangles b.val k.natAbs (code b)
        (properties.windows b k.natAbs) k (by omega) (by omega)
      simpa only [coded] using coordinate
  have denseImage := (fullOrbitInteriors_dense T C closed).mono goodImage
  have closedImage : IsClosed (range (reindexedInteriorCode T C rectangles statuses law code)) :=
    (isCompact_range (reindexedInteriorCode_continuous T C rectangles statuses law code properties.continuous)).isClosed
  apply range_eq_univ.mp
  rw [← closedImage.closure_eq]
  exact denseImage.closure_eq

omit [DiscreteTopology J] in
theorem reindexedInteriorCode_intertwines (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code)
    (a : Path (Transition T (interiorRectangles C))) :
    reindexedInteriorCode T C rectangles statuses law code (shift _ a) =
      T (reindexedInteriorCode T C rectangles statuses law code a) :=
  properties.intertwines (interiorReindexPath T C rectangles statuses law a)

omit [DiscreteTopology J] in
theorem reindexedInteriorCode_finiteFibers (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (x : X) :
    ((reindexedInteriorCode T C rectangles statuses law code) ⁻¹' {x}).Finite := by
  change (interiorReindexPath T C rectangles statuses law ⁻¹' (code ⁻¹' {x})).Finite
  exact Set.Finite.preimage (interiorReindexPath_injective T C rectangles statuses law).injOn
    (properties.finiteFibers x)

omit [DiscreteTopology J] in
theorem reindexedInteriorCode_windows (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code)
    (a : Path (Transition T (interiorRectangles C))) (radius : ℕ) :
    reindexedInteriorCode T C rectangles statuses law code a ∈
      closure (itineraryWindow T (interiorRectangles C) a.val radius) := by
  have windows := properties.windows (interiorReindexPath T C rectangles statuses law a) radius
  simpa only [itineraryWindow, interiorReindexPath, law, Equiv.apply_symm_apply,
    interiorRectangles, reindexedInteriorCode, comp_apply] using windows

omit [DiscreteTopology J] in
theorem reindexedInteriorCode_geometry (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) :
    HasSymbolicFiberGeometry T (interiorRectangles C) (reindexedInteriorCode T C rectangles statuses law code) := by
  constructor
  · intro a b
    constructor
    · intro equal k
      have affiliation := (properties.geometry.1 _ _).mp equal k
      simpa only [Affiliated, interiorReindexPath, law, Equiv.apply_symm_apply, interiorRectangles] using affiliation
    · intro affiliation
      apply (properties.geometry.1 _ _).mpr
      intro k
      simpa only [Affiliated, interiorReindexPath, law, Equiv.apply_symm_apply, interiorRectangles] using affiliation k
  · intro a b equal radius first last k lower upper
    apply Subtype.ext
    apply statuses.symm.injective
    exact properties.geometry.2 (interiorReindexPath T C rectangles statuses law a)
      (interiorReindexPath T C rectangles statuses law b) equal radius
      (congrArg (fun j : InteriorSymbol C => statuses.symm j.val) first)
      (congrArg (fun j : InteriorSymbol C => statuses.symm j.val) last) k lower upper

omit [DiscreteTopology J] in
theorem reindexedInteriorCode_fiber_card (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) (x : X) :
    ((reindexedInteriorCode T C rectangles statuses law code) ⁻¹' {x}).Finite ∧
      ((reindexedInteriorCode T C rectangles statuses law code) ⁻¹' {x}).ncard ≤
        (Fintype.card (InteriorSymbol C)) ^ 2 := by
  apply FiniteEndpointCoding.finite_card_bound (fun a : Path (Transition T (interiorRectangles C)) => a.val)
    (fun a b equal => Subtype.ext equal)
  intro a ha b hb radius first last
  have equal : reindexedInteriorCode T C rectangles statuses law code a =
      reindexedInteriorCode T C rectangles statuses law code b :=
    (show _ = x from ha).trans (show _ = x from hb).symm
  exact (reindexedInteriorCode_geometry T C rectangles statuses law code properties).2
    a b equal radius first last

omit [DiscreteTopology J] in
theorem reindexedInteriorCode_boundary [BaireSpace X] (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code) :
    ∃ B : Set X, IsClosed B ∧ interior B = ∅ ∧
      ∀ a b, reindexedInteriorCode T C rectangles statuses law code a =
        reindexedInteriorCode T C rectangles statuses law code b → a.val 0 ≠ b.val 0 →
          reindexedInteriorCode T C rectangles statuses law code a ∈ B := by
  obtain ⟨B, closed, emptyInterior, boundary⟩ := properties.symbolBoundary
  refine ⟨B, closed, emptyInterior, fun a b equal different => ?_⟩
  apply boundary (interiorReindexPath T C rectangles statuses law a)
    (interiorReindexPath T C rectangles statuses law b) equal
  intro same
  apply different
  apply Subtype.ext
  exact statuses.symm.injective same

omit [TopologicalSpace J] [DiscreteTopology J] [Fintype J] in
theorem interiorReindexPath_window (a b : Path (Transition T (interiorRectangles C))) (n : ℕ)
    (same : WindowAgreement a b n) :
    WindowAgreement (interiorReindexPath T C rectangles statuses law a)
      (interiorReindexPath T C rectangles statuses law b) n := by
  intro k lower upper
  exact congrArg (fun j : InteriorSymbol C => statuses.symm j.val) (same k lower upper)

omit [TopologicalSpace J] [DiscreteTopology J] [Fintype J] in
theorem interiorReindexPath_exponential (φ : Path (Transition T rectangles) → ℝ)
    (variation : HasExponentialVariations φ) :
    HasExponentialVariations (φ ∘ interiorReindexPath T C rectangles statuses law) := by
  obtain ⟨θ, positive, small, H, nonnegative, bound⟩ := variation
  refine ⟨θ, positive, small, H, nonnegative, fun n a b same => ?_⟩
  exact bound n _ _ (interiorReindexPath_window T C rectangles statuses law a b n same)

end LeanShared.FiniteClosedRefinement
