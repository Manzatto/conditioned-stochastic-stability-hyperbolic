module

public import LeanShared.Dynamics.BasicHyperbolicMarkovItineraryCoding
public import LeanShared.Dynamics.FiniteSymbolicRawCodingMultiplicity
public import LeanShared.Dynamics.MarkovCodingProperties

/-! Literal hyperbolic basic data produce a finite-to-one continuous
surjective symbolic Markov coding, with a uniform explicit fiber bound.
The graph consists of actual raw-classifier transitions; whole finite
itinerary closures and the initial coding provenance remain visible.
Holder regularity is a separate quantitative refinement.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Function ThermodynamicDefinitions
open BilateralShadowingCoding ExpansiveLocalProduct FiniteClosedRefinement MarkovFinitePathRealization
open scoped Topology Manifold ContDiff

theorem BasicData.exists_finite_to_one_markov_coding
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
    ∃ N : ℕ, ∃ rectangles : ((Fin N ⊕ ((Fin N × Fin N) × Bool)) → Bool) → Set Λ,
      (∀ status, ∀ x ∈ rectangles status, ∀ y ∈ rectangles status, dist x y < ε) ∧
      ∃ code : Path (Transition S rectangles) → Λ,
        MarkovCodingProperties S rectangles code := by
  classical
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  obtain ⟨c, _positiveC, τ, positiveτ, smaller, small, expansive,
    N, R, center, initialCode, bracket, _continuousInitial, onto, nearInitial, intertwinesInitial,
    _compact, _continuousBracket, bounds, idempotent, band, closed, cover, atomDiameter,
    _regularizedCover, _forwardRaw⟩ :=
    b.exists_raw_markov_refinement forward inverse (ε / 4) (by positivity)
  let atoms := fun status => atom (codedClassifiers initialCode bracket) status
  let default : Λ := Classical.choice (Set.nonempty_coe_sort.mpr b.nonempty)
  let refinedCenter := fun status =>
    if h : (atoms status).Nonempty then Classical.choose h else default
  have nearCenter (status) (x : Λ) (hx : x ∈ atoms status) :
      dist x (refinedCenter status) ≤ 2 * τ := by
    have nonempty : (atoms status).Nonempty := ⟨x, hx⟩
    have centerInside : refinedCenter status ∈ atoms status := by
      simp only [refinedCenter, dite_eq_left nonempty]
      exact Classical.choose_spec nonempty
    exact atomDiameter status x hx _ centerInside
  have realized (word : ℕ → ((Fin N ⊕ ((Fin N × Fin N) × Bool)) → Bool))
      (length : ℕ) (initial : (atoms (word 0)).Nonempty)
      (edges : ∀ j < length, Transition S atoms (word j) (word (j + 1))) :
      ∃ x : Λ, ∀ j ≤ length, (S : Λ → Λ)^[j] x ∈ atoms (word j) :=
    codedAtom_finite_path_realized S center initialCode onto c τ positiveτ.le expansive (by linarith)
      nearInitial intertwinesInitial bracket bounds idempotent band word length initial edges
  obtain ⟨code, continuousCode, codeOnto, _nearCode, codeIntertwines, windows⟩ :=
    exists_itinerary_coding S atoms refinedCenter c (2 * τ) expansive (by linarith) cover nearCenter realized
  have smallAtoms : ∀ status, ∀ x ∈ atom (codedClassifiers initialCode bracket) status,
      ∀ y ∈ atom (codedClassifiers initialCode bracket) status, dist x y < ε := by
    intro status x hx y hy
    have estimate := codedAtom_small initialCode onto bracket (2 * τ)
      (fun i x hx y hy => rectangle_diameter S center initialCode τ nearInitial i x y hx hy) status x hx y hy
    linarith
  have diameter := codedAtom_small initialCode onto bracket (2 * τ)
    (fun i x hx y hy => rectangle_diameter S center initialCode τ nearInitial i x y hx hy)
  have geometry : HasSymbolicFiberGeometry S
      (fun status => atom (codedClassifiers initialCode bracket) status) code := by
    constructor
    · exact coding_eq_iff_affiliated S _ (2 * τ) c expansive (by linarith) diameter code windows
    · exact coding_no_diamonds S _ (2 * τ)
        (raw_atom_stable_forward S center initialCode c τ positiveτ.le expansive (by linarith)
          nearInitial intertwinesInitial bracket bounds idempotent band)
        (raw_atom_unstable_inverse S center initialCode c τ positiveτ.le expansive (by linarith)
          nearInitial intertwinesInitial bracket bounds idempotent band)
        c expansive (by linarith) (fun s t different => atom_disjoint _ s t different) diameter
        (codedAtom_product S initialCode onto c (2 * τ) expansive (by linarith) bracket bounds idempotent band)
        code windows
  have fibers (x : Λ) : (code ⁻¹' {x}).Finite ∧ (code ⁻¹' {x}).ncard ≤
      (Fintype.card ((Fin N ⊕ ((Fin N × Fin N) × Bool)) → Bool)) ^ 2 :=
    codedAtom_fiber_finite_card S center initialCode onto c τ positiveτ.le expansive (by linarith)
      nearInitial intertwinesInitial bracket bounds idempotent band code windows x
  exact ⟨N, atoms, smallAtoms, code,
    ⟨continuousCode, codeOnto, codeIntertwines, windows, geometry, fibers,
      raw_atoms_have_closed_classifier_origin _ closed⟩⟩

end LeanShared.HyperbolicBasicSet
