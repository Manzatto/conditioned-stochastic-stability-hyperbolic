module

public import LeanShared.Dynamics.RectangleFourWayRefinement
import Mathlib.Tactic.Linarith

/-! A common actual expansivity scale makes every initial rectangle
bracket agree on overlaps.  Thus intersecting initial rectangles are
rectangles for the same bracket, as needed by the four-way refinement.
-/

public noncomputable section
namespace LeanShared.ExpansiveLocalProduct
open Set Function RectangleFourWayRefinement
open scoped Topology
variable {X : Type*} [MetricSpace X]

theorem bracket_overlap (T : X ≃ₜ X) (c δ : ℝ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c) (R S : Set X)
    (left : R × R → R) (right : S × S → S)
    (leftBound : ∀ p, ProductRelation T δ p.1.val p.2.val (left p).val)
    (rightBound : ∀ p, ProductRelation T δ p.1.val p.2.val (right p).val)
    (x y : X) (hx : x ∈ R) (hy : y ∈ R) (hx' : x ∈ S) (hy' : y ∈ S) :
    (left (⟨x, hx⟩, ⟨y, hy⟩)).val = (right (⟨x, hx'⟩, ⟨y, hy'⟩)).val :=
  product_unique T c δ expansive small x y _ _ (leftBound _) (rightBound _)

omit [MetricSpace X] in
/-- An overlap is a rectangle for the first bracket because both actual
brackets agree there. -/
theorem overlap_isRectangle {I : Type*} (rectangles : I → Set X)
    (bracket : ∀ i, rectangles i × rectangles i → rectangles i)
    (compatible : ∀ i j (x y : X) (hx : x ∈ rectangles i) (hy : y ∈ rectangles i)
      (hx' : x ∈ rectangles j) (hy' : y ∈ rectangles j),
      (bracket i (⟨x, hx⟩, ⟨y, hy⟩)).val = (bracket j (⟨x, hx'⟩, ⟨y, hy'⟩)).val)
    (i j : I) : IsRectangle (bracket i) {x : rectangles i | x.val ∈ rectangles j} := by
  intro x hx y hy
  change (bracket i (x, y)).val ∈ rectangles j
  rw [compatible i j x.val y.val x.property y.property hx hy]
  exact (bracket j (⟨x.val, hx⟩, ⟨y.val, hy⟩)).property

end LeanShared.ExpansiveLocalProduct

namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions ExpansiveLocalProduct
open scoped Topology Manifold ContDiff

/-- Actual small initial rectangles have a simultaneous compatible bracket
family.  The common scale is derived from the actual expansivity radius. -/
theorem BasicData.exists_compatible_rectangle_brackets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ δ > 0, δ < ε ∧ ∃ N : ℕ, ∃ rectangles : Fin N → Set Λ,
      ∃ bracket : ∀ i, rectangles i × rectangles i → rectangles i,
        (⋃ i, rectangles i) = univ ∧
        (∀ i, IsCompact (rectangles i) ∧
          (∀ x ∈ rectangles i, ∀ y ∈ rectangles i, dist x y ≤ δ) ∧
          Continuous (bracket i) ∧
          (∀ p, ProductRelation (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant)
            δ p.1.val p.2.val (bracket i p).val) ∧
          (∀ x : rectangles i, bracket i (x, x) = x) ∧
          ∀ x y u v : rectangles i,
            bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v)) ∧
        ∀ i j (x y : Λ) (hx : x ∈ rectangles i) (hy : y ∈ rectangles i)
          (hx' : x ∈ rectangles j) (hy' : y ∈ rectangles j),
          (bracket i (⟨x, hx⟩, ⟨y, hy⟩)).val = (bracket j (⟨x, hx'⟩, ⟨y, hy'⟩)).val := by
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
  have positiveScale : 0 < scale := lt_min positiveε (by positivity)
  obtain ⟨δ, positiveδ, smaller, N, rectangles, cover, properties⟩ :=
    b.exists_finite_rectangle_brackets forward inverse scale positiveScale
  have small : 2 * δ ≤ c := by
    have bound : scale ≤ c / 4 := min_le_right _ _
    linarith
  choose bracket continuous bounds idempotent band using fun i => (properties i).2.2
  refine ⟨δ, positiveδ, smaller.trans_le (min_le_left _ _), N, rectangles, bracket, cover, ?_, ?_⟩
  · intro i
    exact ⟨(properties i).1, (properties i).2.1, continuous i, bounds i, idempotent i, band i⟩
  · intro i j x y hx hy hx' hy'
    exact bracket_overlap S c δ expansiveS small (rectangles i) (rectangles j)
      (bracket i) (bracket j) (bounds i) (bounds j) x y hx hy hx' hy'

end LeanShared.HyperbolicBasicSet
