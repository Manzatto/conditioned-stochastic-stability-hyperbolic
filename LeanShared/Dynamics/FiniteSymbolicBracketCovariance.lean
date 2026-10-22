module

public import LeanShared.Dynamics.FiniteSymbolicWeakTransitions

/-! Bracket covariance along a literal coded branch.  The weak symbolic
transition gives membership of the image bracket; all inverse times are
controlled by the product bound, including time zero by the target
cylinder diameter.  Local stable/unstable slices are also identified with
the corresponding bracket equations using actual expansivity.
-/

public noncomputable section
namespace LeanShared.ExpansiveLocalProduct
open Set
variable {X : Type*} [MetricSpace X]

theorem stable_iff_bracket (T : X ≃ₜ X) (c δ : ℝ) (nonnegativeδ : 0 ≤ δ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c) (R : Set X) (bracket : R × R → R)
    (bounds : ∀ p, ProductRelation T δ p.1.val p.2.val (bracket p).val) (x y : R) :
    (∀ j : ℕ, dist ((T : X → X)^[j] y.val) ((T : X → X)^[j] x.val) ≤ δ) ↔
      bracket (x, y) = y := by
  constructor
  · intro stable
    apply Subtype.ext
    apply product_unique T c δ expansive small x.val y.val _ _ (bounds _)
    intro j
    exact ⟨stable j, by simpa only [dist_self] using nonnegativeδ⟩
  · intro equal j
    have estimate := (bounds (x, y) j).1
    simpa only [equal] using estimate

theorem unstable_iff_bracket (T : X ≃ₜ X) (c δ : ℝ) (nonnegativeδ : 0 ≤ δ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c) (R : Set X) (bracket : R × R → R)
    (bounds : ∀ p, ProductRelation T δ p.1.val p.2.val (bracket p).val) (x y : R) :
    (∀ j : ℕ, dist ((T.symm : X → X)^[j] x.val) ((T.symm : X → X)^[j] y.val) ≤ δ) ↔
      bracket (x, y) = x := by
  constructor
  · intro unstable
    apply Subtype.ext
    apply product_unique T c δ expansive small x.val y.val _ _ (bounds _)
    intro j
    exact ⟨by simpa only [dist_self] using nonnegativeδ, unstable j⟩
  · intro equal j
    have estimate := (bounds (x, y) j).2
    simpa only [equal] using estimate

end LeanShared.ExpansiveLocalProduct

namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit ExpansiveLocalProduct
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

/-- A product point maps to the product point along the chosen symbolic transition. -/
theorem product_forward_on_branch (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
    (c ε : ℝ) (nonnegativeε : 0 ≤ ε)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (intertwines : ∀ a, code (shift R a) = T (code a))
    (a : Path R) (y z : X)
    (insideZ : z ∈ rectangle code (a.val 0)) (insideTy : T y ∈ rectangle code (a.val 1))
    (product : ProductRelation T (2 * ε) (code a) y z) :
    T z ∈ rectangle code (a.val 1) ∧
      ProductRelation T (2 * ε) (T (code a)) (T y) (T z) := by
  have stable : ∀ j : ℕ, dist ((T : X → X)^[j] z) ((T : X → X)^[j] (code a)) ≤ 2 * ε :=
    fun j => (product j).1
  obtain ⟨insideTz, forward⟩ := weak_stable_transition T center code c ε nonnegativeε expansive small
    near intertwines a z insideZ stable
  refine ⟨insideTz, fun j => ⟨forward j, ?_⟩⟩
  cases j with
  | zero =>
    simpa only [Function.iterate_zero_apply] using
      rectangle_diameter T center code ε near (a.val 1) (T z) (T y) insideTz insideTy
  | succ j =>
    simpa only [Function.iterate_succ_apply, T.symm_apply_apply] using (product j).2

/-- Exact covariance of the two actual rectangle brackets on a coded branch. -/
theorem bracket_forward_on_branch (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
    (c ε : ℝ) (nonnegativeε : 0 ≤ ε)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (intertwines : ∀ a, code (shift R a) = T (code a)) (a : Path R)
    (left : rectangle code (a.val 0) × rectangle code (a.val 0) → rectangle code (a.val 0))
    (right : rectangle code (a.val 1) × rectangle code (a.val 1) → rectangle code (a.val 1))
    (leftBound : ∀ p, ProductRelation T (2 * ε) p.1.val p.2.val (left p).val)
    (rightBound : ∀ p, ProductRelation T (2 * ε) p.1.val p.2.val (right p).val)
    (y : X) (insideY : y ∈ rectangle code (a.val 0)) (insideTy : T y ∈ rectangle code (a.val 1)) :
    T (left (⟨code a, ⟨a, rfl, rfl⟩⟩, ⟨y, insideY⟩)).val =
      (right (⟨T (code a), ⟨shift R a, rfl, intertwines a⟩⟩,
        ⟨T y, insideTy⟩)).val := by
  let x : rectangle code (a.val 0) := ⟨code a, ⟨a, rfl, rfl⟩⟩
  let v := left (x, ⟨y, insideY⟩)
  have product := leftBound (x, ⟨y, insideY⟩)
  have image := product_forward_on_branch T center code c ε nonnegativeε expansive small near intertwines
    a y v.val v.property insideTy product
  exact product_unique T c (2 * ε) expansive (by linarith) _ _ _ _ image.2 (rightBound _)

end LeanShared.BilateralShadowingCoding
