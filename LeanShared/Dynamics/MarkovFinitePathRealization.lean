module

public import LeanShared.Dynamics.FiniteSymbolicAtomProducts
public import LeanShared.Dynamics.FiniteSymbolicInverseAtomTransitions

/-! Every finite path in a graph defined by actual rectangle transitions
is realized by an orbit segment.  The proof uses actual product points
and the two local Markov inclusions, pulling a product point backward
through the already realized prefix.  No global coding or multiplicity
claim is assumed.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function ExpansiveLocalProduct
variable {X I : Type*} [MetricSpace X]

/-- The directed edge relation supplied by actual one-step intersections. -/
@[expose] def Transition (T : X ≃ₜ X) (rectangles : I → Set X) (i j : I) : Prop :=
  ∃ x ∈ rectangles i, T x ∈ rectangles j

variable (T : X ≃ₜ X) (rectangles : I → Set X) (δ : ℝ)
    (inverse : ∀ i j x y, x ∈ rectangles i → y ∈ rectangles i → T.symm x ∈ rectangles j →
      (∀ n : ℕ, dist ((T.symm : X → X)^[n] y) ((T.symm : X → X)^[n] x) ≤ δ) →
      T.symm y ∈ rectangles j ∧
        ∀ n : ℕ, dist ((T.symm : X → X)^[n] (T.symm y))
          ((T.symm : X → X)^[n] (T.symm x)) ≤ δ)
include inverse

/-- Pull an unstable slice through a finite, already realized itinerary. -/
theorem unstable_lift_prefix (word : ℕ → I) (points : ℕ → X)
    (coherent : ∀ n, T (points n) = points (n + 1)) (length : ℕ)
    (inside : ∀ k ≤ length, points k ∈ rectangles (word k)) (w : X)
    (insideW : w ∈ rectangles (word length))
    (unstable : ∀ n : ℕ,
      dist ((T.symm : X → X)^[n] w) ((T.symm : X → X)^[n] (points length)) ≤ δ) :
    ∃ v : X, (T : X → X)^[length] v = w ∧
      ∀ k ≤ length, (T : X → X)^[k] v ∈ rectangles (word k) := by
  induction length generalizing w with
  | zero => exact ⟨w, rfl, fun k hk => by simpa only [Nat.eq_zero_of_le_zero hk, iterate_zero_apply] using insideW⟩
  | succ length ih =>
    have previous : T.symm (points (length + 1)) = points length := by
      rw [← coherent length, T.symm_apply_apply]
    have pulled := inverse (word (length + 1)) (word length) (points (length + 1)) w
      (inside _ le_rfl) insideW (previous.symm ▸ inside length (by omega)) unstable
    have past : ∀ n : ℕ, dist ((T.symm : X → X)^[n] (T.symm w))
        ((T.symm : X → X)^[n] (points length)) ≤ δ := by
      simpa only [previous] using pulled.2
    obtain ⟨v, image, itinerary⟩ := ih (fun k hk => inside k (by omega)) (T.symm w) pulled.1 past
    refine ⟨v, ?_, fun k hk => ?_⟩
    · rw [iterate_succ_apply', image, T.apply_symm_apply]
    · by_cases smaller : k ≤ length
      · exact itinerary k smaller
      · have equal : k = length + 1 := by omega
        subst k
        rw [iterate_succ_apply', image, T.apply_symm_apply]
        exact insideW

/-- Every finite admissible word is an actual orbit itinerary. -/
theorem finite_path_realized
    (forward : ∀ i j x y, x ∈ rectangles i → y ∈ rectangles i → T x ∈ rectangles j →
      (∀ n : ℕ, dist ((T : X → X)^[n] y) ((T : X → X)^[n] x) ≤ δ) →
      T y ∈ rectangles j ∧
        ∀ n : ℕ, dist ((T : X → X)^[n] (T y)) ((T : X → X)^[n] (T x)) ≤ δ)
    (product : ∀ i x y, x ∈ rectangles i → y ∈ rectangles i →
      ∃ z ∈ rectangles i, ProductRelation T δ x y z)
    (word : ℕ → I) (length : ℕ) (initial : (rectangles (word 0)).Nonempty)
    (edges : ∀ k < length, Transition T rectangles (word k) (word (k + 1))) :
    ∃ x : X, ∀ k ≤ length, (T : X → X)^[k] x ∈ rectangles (word k) := by
  induction length with
  | zero =>
    obtain ⟨x, hx⟩ := initial
    exact ⟨x, fun k hk => by simpa only [Nat.eq_zero_of_le_zero hk, iterate_zero_apply] using hx⟩
  | succ length ih =>
    obtain ⟨y, earlier⟩ := ih (fun k hk => edges k (by omega))
    obtain ⟨z, insideZ, imageZ⟩ := edges length (by omega)
    obtain ⟨w, insideW, relation⟩ := product (word length) z ((T : X → X)^[length] y)
      insideZ (earlier length le_rfl)
    have imageW : T w ∈ rectangles (word (length + 1)) :=
      (forward (word length) (word (length + 1)) z w insideZ insideW imageZ (fun n => (relation n).1)).1
    obtain ⟨x, image, itinerary⟩ := unstable_lift_prefix T rectangles δ inverse word
      (fun k => (T : X → X)^[k] y) (fun k => (iterate_succ_apply' _ _ _).symm)
      length earlier w insideW (fun n => (relation n).2)
    refine ⟨x, fun k hk => ?_⟩
    by_cases smaller : k ≤ length
    · exact itinerary k smaller
    · have equal : k = length + 1 := by omega
      subst k
      rw [iterate_succ_apply', image]
      exact imageW

end LeanShared.MarkovFinitePathRealization

namespace LeanShared.BilateralShadowingCoding
open Set Function ExpansiveLocalProduct FiniteClosedRefinement MarkovFinitePathRealization
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

/-- Finite paths in the actual raw classifier graph are realized;
all dynamical and product premises are derived from the original code. -/
theorem codedAtom_finite_path_realized (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
    (onto : Surjective code) (c ε : ℝ) (nonnegativeε : 0 ≤ ε)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (BilateralHomeomorphismOrbit.orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (intertwines : ∀ a, code (shift R a) = T (code a))
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (bounds : ∀ i p, ProductRelation T (2 * ε) p.1.val p.2.val (bracket i p).val)
    (idempotent : ∀ i (x : rectangle code i), bracket i (x, x) = x)
    (band : ∀ i (x y u v : rectangle code i),
      bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v))
    (word : ℕ → ((A ⊕ ((A × A) × Bool)) → Bool)) (length : ℕ)
    (initial : (atom (codedClassifiers code bracket) (word 0)).Nonempty)
    (edges : ∀ k < length, Transition T (fun status => atom (codedClassifiers code bracket) status)
      (word k) (word (k + 1))) :
    ∃ x : X, ∀ k ≤ length, (T : X → X)^[k] x ∈ atom (codedClassifiers code bracket) (word k) := by
  exact finite_path_realized T (fun status => atom (codedClassifiers code bracket) status) (2 * ε)
    (raw_atom_unstable_inverse T center code c ε nonnegativeε expansive small near intertwines
      bracket bounds idempotent band)
    (raw_atom_stable_forward T center code c ε nonnegativeε expansive small near intertwines
      bracket bounds idempotent band)
    (codedAtom_product T code onto c (2 * ε) expansive (by linarith) bracket bounds idempotent band)
    word length initial edges

end LeanShared.BilateralShadowingCoding
