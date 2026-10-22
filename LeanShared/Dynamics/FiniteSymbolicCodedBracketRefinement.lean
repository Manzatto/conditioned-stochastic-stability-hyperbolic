module

public import LeanShared.Dynamics.FiniteSymbolicAtomTransitions
public import LeanShared.Dynamics.RectangleBracketAlgebra

/-! Continuous brackets and closed finite classifiers on the literal
finite-graph cylinder cover.  The graph and coding are retained when
forming the raw atoms and their proper topological regularizations.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit ExpansiveLocalProduct
open RectangleFourWayRefinement FiniteClosedRefinement
open scoped Topology
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

/-- Symbolic splicing produces continuous rectangular-band brackets on
the actual cylinder images, at the same quantitative shadowing scale. -/
theorem exists_coded_brackets [DiscreteTopology A] [CompactSpace A]
    (T : X ≃ₜ X) (center : A → X) (code : Path R → X) (continuous : Continuous code)
    (c ε : ℝ) (positiveε : 0 < ε)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 6 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε) :
    ∃ bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i,
      (∀ i, Continuous (bracket i)) ∧
      (∀ i p, ProductRelation T (2 * ε) p.1.val p.2.val (bracket i p).val) ∧
      (∀ i (x : rectangle code i), bracket i (x, x) = x) ∧
      ∀ i (x y u v : rectangle code i),
        bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v) := by
  have existence (i : A) := exists_continuous_rectangle_bracket T c (2 * ε) (rectangle code i)
    (rectangle_compact code continuous i) (by positivity) expansive (by linarith)
    (fun x hx y hy => rectangle_product_unique T center code c ε expansive (by linarith) near i x y hx hy)
  choose bracket continuousBracket bounds idempotent band using existence
  exact ⟨bracket, continuousBracket, bounds, idempotent, band⟩

omit [TopologicalSpace A] in
/-- The finite classifiers are closed; their raw atoms therefore admit the proved proper
regularization and boundary conclusions. -/
theorem codedClassifiers_isClosed (code : Path R → X)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (compact : ∀ i, IsCompact (rectangle code i))
    (continuous : ∀ i, Continuous (bracket i))
    (idempotent : ∀ i (x : rectangle code i), bracket i (x, x) = x)
    (band : ∀ i (x y u v : rectangle code i),
      bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v))
    (k : A ⊕ ((A × A) × Bool)) : IsClosed (codedClassifiers code bracket k) := by
  cases k with
  | inl i => exact (compact i).isClosed
  | inr k =>
    rcases k with ⟨⟨i, j⟩, kind⟩
    let : CompactSpace (rectangle code i) := isCompact_iff_compactSpace.mp (compact i)
    have intersectionClosed : IsClosed {z : rectangle code i | z.val ∈ rectangle code j} :=
      (compact j).isClosed.preimage continuous_subtype_val
    cases kind
    · have closedHit := stableHit_isClosed (bracket i) (idempotent i) (band i)
        (continuous i) _ intersectionClosed
      have imageClosed := (closedHit.isCompact.image
        (continuous_subtype_val : Continuous (Subtype.val : rectangle code i → X))).isClosed
      convert imageClosed using 1
      ext x
      constructor
      · rintro ⟨hx, hit⟩
        exact ⟨⟨x, hx⟩, hit, rfl⟩
      · rintro ⟨z, hit, rfl⟩
        exact ⟨z.property, hit⟩
    · have closedHit := unstableHit_isClosed (bracket i) (idempotent i) (band i)
        (continuous i) _ intersectionClosed
      have imageClosed := (closedHit.isCompact.image
        (continuous_subtype_val : Continuous (Subtype.val : rectangle code i → X))).isClosed
      convert imageClosed using 1
      ext x
      constructor
      · rintro ⟨hx, hit⟩
        exact ⟨⟨x, hx⟩, hit, rfl⟩
      · rintro ⟨z, hit, rfl⟩
        exact ⟨z.property, hit⟩

omit [TopologicalSpace A] in
theorem codedAtom_small (code : Path R → X) (onto : Surjective code)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (δ : ℝ) (diameter : ∀ i, ∀ x ∈ rectangle code i, ∀ y ∈ rectangle code i, dist x y ≤ δ)
    (status : (A ⊕ ((A × A) × Bool)) → Bool) :
    ∀ x ∈ atom (codedClassifiers code bracket) status,
      ∀ y ∈ atom (codedClassifiers code bracket) status, dist x y ≤ δ := by
  intro x hx y hy
  obtain ⟨a, coded⟩ := onto x
  have insideX : x ∈ rectangle code (a.val 0) := ⟨a, rfl, coded⟩
  have insideY : y ∈ rectangle code (a.val 0) :=
    (atom_membership_agrees _ status x y hx hy (.inl (a.val 0))).mp insideX
  exact diameter (a.val 0) x insideX y insideY

end LeanShared.BilateralShadowingCoding

namespace LeanShared.FiniteClosedRefinement
open Set
variable {X I : Type*} [TopologicalSpace X]

omit [TopologicalSpace X] in
/-- The literal membership atoms cover, without topological hypotheses. -/
theorem atom_cover (classifiers : I → Set X) : (⋃ status : I → Bool, atom classifiers status) = univ := by
  classical
  apply eq_univ_of_forall
  intro x
  refine mem_iUnion.mpr ⟨fun i => decide (x ∈ classifiers i), ?_⟩
  apply (mem_atom_iff _ _ x).mpr
  intro i
  exact decide_eq_true_iff.symm

end LeanShared.FiniteClosedRefinement
