module

public import LeanShared.Dynamics.LocalBracketInterior
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.Linarith

/-! Actual proper initial rectangles: a nonempty finite compact cover,
each member equal to the closure of its ambient interior, with a common
continuous local bracket.  No disjointness or Markov inclusion is assumed
or asserted; these are the initial rectangles for the next refinement.
-/

public noncomputable section
namespace LeanShared.ExpansiveLocalProduct
variable {X : Type*} [MetricSpace X] {T : X ≃ₜ X} {δ ρ : ℝ} {x y z : X}

theorem ProductRelation.mono (relation : ProductRelation T ρ x y z) (larger : ρ ≤ δ) :
    ProductRelation T δ x y z :=
  fun j => ⟨(relation j).1.trans larger, (relation j).2.trans larger⟩

end LeanShared.ExpansiveLocalProduct

namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions ExpansiveLocalProduct
open scoped Topology Manifold ContDiff

/-- The literal basic data produce a finite cover by nonempty proper
rectangles with a common continuous local product and exact boundary properties. -/
theorem BasicData.exists_finite_proper_rectangles
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ δ > 0, δ < ε ∧ ∃ η > 0,
      ∃ bracket : NearbyPairs (X := Λ) η → Λ,
        Continuous bracket ∧ ConditionalBand bracket ∧
        (∀ (x : Λ) (h : dist x x < η), bracket ⟨(x, x), h⟩ = x) ∧
        (∀ p, ProductRelation (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant)
          δ p.val.1 p.val.2 (bracket p)) ∧
        ∃ N : ℕ, ∃ rectangles : Fin N → Set Λ,
          (⋃ i, rectangles i) = univ ∧ ∀ i,
            IsCompact (rectangles i) ∧ (rectangles i).Nonempty ∧
            (interior (rectangles i)).Nonempty ∧
            rectangles i = closure (interior (rectangles i)) ∧
            (∀ x ∈ rectangles i, ∀ y ∈ rectangles i, dist x y < η ∧ dist x y < δ) ∧
            IsLocalRectangle bracket (rectangles i) ∧
            frontier (rectangles i) = rectangles i \ interior (rectangles i) ∧
            interior (frontier (rectangles i)) = ∅ := by
  classical
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  have forwardS (x : Λ) : (S x).val = T x.val := rfl
  have backwardS (x : Λ) : (S.symm x).val = T.symm x.val := rfl
  obtain ⟨c, positiveC, expansive⟩ := b.exists_expansivity_radius forward inverse
  have expansiveS : ∀ x y : Λ, (∀ j : ℕ,
      dist ((S : Λ → Λ)^[j] x) ((S : Λ → Λ)^[j] y) ≤ c ∧
      dist ((S.symm : Λ → Λ)^[j] x) ((S.symm : Λ → Λ)^[j] y) ≤ c) → x = y := by
    intro x y close
    apply Subtype.ext
    apply expansive x.val x.property y.val y.property
    intro j
    have estimate := close j
    change dist (((S : Λ → Λ)^[j] x).val) (((S : Λ → Λ)^[j] y).val) ≤ c ∧
      dist (((S.symm : Λ → Λ)^[j] x).val) (((S.symm : Λ → Λ)^[j] y).val) ≤ c at estimate
    simpa only [iterate_coe_restriction S forwardS, iterate_coe_restriction S.symm backwardS]
      using estimate
  let scale := min ε (c / 4)
  obtain ⟨δ, positiveδ, smaller, η, positiveη, _radiusBound, bracket, continuous, bounds, idempotent⟩ :=
    b.exists_continuous_local_product forward inverse scale (lt_min positiveε (by positivity))
  have small₃ : 3 * δ ≤ c := by
    have bound : scale ≤ c / 4 := min_le_right _ _
    linarith
  have small₂ : 2 * δ ≤ c := by linarith
  have band : ConditionalBand bracket := conditionalBand_of_product S c δ expansiveS small₃ bracket bounds
  obtain ⟨ρ, positiveρ, smallρ, N, initial, cover, properties⟩ :=
    b.exists_finite_rectangle_brackets forward inverse (min η δ) (lt_min positiveη positiveδ)
  have ρη : ρ < η := smallρ.trans_le (min_le_left _ _)
  have ρδ : ρ < δ := smallρ.trans_le (min_le_right _ _)
  have localRectangle (i : Fin N) : IsLocalRectangle bracket (initial i) := by
    intro x hx y hy hxy
    obtain ⟨localMap, _localContinuous, localBounds, _localIdempotent, _localBand⟩ := (properties i).2.2
    have localRelation := (localBounds (⟨x, hx⟩, ⟨y, hy⟩)).mono ρδ.le
    have equal := product_unique S c δ expansiveS small₂ x y _ _ (bounds ⟨(x, y), hxy⟩) localRelation
    rw [equal]
    exact (localMap (⟨x, hx⟩, ⟨y, hy⟩)).property
  have smallInitial (i : Fin N) : ∀ x ∈ initial i, ∀ y ∈ initial i, dist x y < η :=
    fun x hx y hy => ((properties i).2.1 x hx y hy).trans_lt ρη
  let proper : Fin N → Set Λ := fun i => closure (interior (initial i))
  have subset (i : Fin N) : proper i ⊆ initial i := (properties i).1.isClosed.closure_interior_subset
  have compact (i : Fin N) : IsCompact (proper i) :=
    (properties i).1.of_isClosed_subset isClosed_closure (subset i)
  have properEq (i : Fin N) : proper i = closure (interior (proper i)) :=
    closure_interior_idem.symm
  have localProper (i : Fin N) : IsLocalRectangle bracket (proper i) :=
    IsLocalRectangle.regularize positiveη bracket idempotent band continuous (initial i)
      (localRectangle i) (smallInitial i)
  have coverProper : (⋃ i, proper i) = univ := by
    have dense := dense_iUnion_interior_of_closed (fun i => (properties i).1.isClosed) cover
    change (⋃ i, closure (interior (initial i))) = univ
    rw [← closure_iUnion_of_finite]
    exact dense.closure_eq
  let J := {i : Fin N // (proper i).Nonempty}
  let : Fintype J := Fintype.ofFinite J
  let K := Fintype.card J
  let e : Fin K ≃ J := (Fintype.equivFin J).symm
  let rectangles : Fin K → Set Λ := fun i => proper (e i).val
  have finalCover : (⋃ i, rectangles i) = univ := by
    apply eq_univ_of_forall
    intro x
    have inside : x ∈ ⋃ i, proper i := coverProper.symm ▸ mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp inside
    refine mem_iUnion.mpr ⟨e.symm ⟨i, ⟨x, hi⟩⟩, ?_⟩
    simpa only [rectangles, Equiv.apply_symm_apply] using hi
  refine ⟨δ, positiveδ, smaller.trans_le (min_le_left _ _), η, positiveη,
    bracket, continuous, band, idempotent, bounds, K, rectangles, finalCover, ?_⟩
  intro i
  have nonempty : (rectangles i).Nonempty := (e i).property
  have properFinal : rectangles i = closure (interior (rectangles i)) := properEq (e i).val
  have compactFinal : IsCompact (rectangles i) := compact (e i).val
  have interiorNonempty : (interior (rectangles i)).Nonempty := by
    rw [properFinal] at nonempty
    exact nonempty.of_closure
  refine ⟨compactFinal, (e i).property, interiorNonempty, properFinal, ?_,
    localProper (e i).val, compactFinal.isClosed.frontier_eq, interior_frontier compactFinal.isClosed⟩
  intro x hx y hy
  have estimate := (properties (e i).val).2.1 x (subset _ hx) y (subset _ hy)
  exact ⟨estimate.trans_lt ρη, estimate.trans_lt ρδ⟩

end LeanShared.HyperbolicBasicSet
