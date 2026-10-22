module

public import LeanShared.Dynamics.MarkovCodingFiniteFibers

/-! Uniform bounded multiplicity for the actual raw-classifier coding.
Every premise of the general no-diamonds theorem is derived from the
original literal graph code and its proved symbolic splicing geometry.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit ExpansiveLocalProduct
open FiniteClosedRefinement MarkovFinitePathRealization
variable {A X : Type*} [TopologicalSpace A] [Fintype A] [DecidableEq A] [MetricSpace X] {R : A → A → Prop}

theorem codedAtom_fiber_finite_card (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
    (onto : Surjective code) (c ε : ℝ) (nonnegativeε : 0 ≤ ε)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (intertwines : ∀ a, code (shift R a) = T (code a))
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (bounds : ∀ i p, ProductRelation T (2 * ε) p.1.val p.2.val (bracket i p).val)
    (idempotent : ∀ i (x : rectangle code i), bracket i (x, x) = x)
    (band : ∀ i (x y u v : rectangle code i),
      bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v))
    (refinedCode : Path (Transition T (fun status => atom (codedClassifiers code bracket) status)) → X)
    (windows : ∀ a radius, refinedCode a ∈
      closure (itineraryWindow T (fun status => atom (codedClassifiers code bracket) status) a.val radius))
    (x : X) :
    (refinedCode ⁻¹' {x}).Finite ∧ (refinedCode ⁻¹' {x}).ncard ≤
      (Fintype.card ((A ⊕ ((A × A) × Bool)) → Bool)) ^ 2 := by
  apply coding_fiber_finite_card T (fun status => atom (codedClassifiers code bracket) status) (2 * ε)
    (raw_atom_stable_forward T center code c ε nonnegativeε expansive small near intertwines bracket bounds idempotent band)
    (raw_atom_unstable_inverse T center code c ε nonnegativeε expansive small near intertwines bracket bounds idempotent band)
    c expansive (by linarith) (fun s t different => atom_disjoint _ s t different)
    (codedAtom_small code onto bracket (2 * ε) (fun i x hx y hy => rectangle_diameter T center code ε near i x y hx hy))
    (codedAtom_product T code onto c (2 * ε) expansive (by linarith) bracket bounds idempotent band)
    refinedCode windows x

end LeanShared.BilateralShadowingCoding
