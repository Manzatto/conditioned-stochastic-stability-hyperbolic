module

public import LeanShared.Dynamics.FiniteSymbolicRectangles
public import LeanShared.Dynamics.ExpansiveLocalProduct
import Mathlib.Tactic.Linarith

/-! Continuous brackets and their rectangular-band algebra are produced
on the actual small compact rectangles.  This is the algebra needed for
the stable/unstable four-way refinement, not a Markov partition assumption.
-/

public noncomputable section
namespace LeanShared.ExpansiveLocalProduct
open Set Function
open scoped Topology
variable {X : Type*} [MetricSpace X]

/-- The local product of a sufficiently small compact rectangle is a
continuous rectangular-band operation. -/
theorem exists_continuous_rectangle_bracket (T : X ≃ₜ X) (c δ : ℝ) (R : Set X)
    (compact : IsCompact R) (positiveδ : 0 < δ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 3 * δ ≤ c)
    (product : ∀ x ∈ R, ∀ y ∈ R, ∃! z : X,
      z ∈ R ∧ ProductRelation T δ x y z) :
    ∃ bracket : R × R → R, Continuous bracket ∧
      (∀ p, ProductRelation T δ p.1.val p.2.val (bracket p).val) ∧
      (∀ x : R, bracket (x, x) = x) ∧
      ∀ x y u v : R, bracket (bracket (x, y), bracket (u, v)) = bracket (x, v) := by
  let : CompactSpace R := isCompact_iff_compactSpace.mp compact
  have choice (p : R × R) : ∃ z : R, ProductRelation T δ p.1.val p.2.val z.val := by
    obtain ⟨z, inside, _unique⟩ := product p.1.val p.1.property p.2.val p.2.property
    exact ⟨⟨z, inside.1⟩, inside.2⟩
  choose bracket bounds using choice
  have small₂ : 2 * δ ≤ c := by linarith
  have unique (p : R × R) (z : R) (hz : ProductRelation T δ p.1.val p.2.val z.val) :
      bracket p = z :=
    Subtype.ext (product_unique T c δ expansive small₂ _ _ _ _ (bounds p) hz)
  have graph : IsClosed bracket.graph := by
    have identity : bracket.graph = ⋂ j : ℕ,
        {p : (R × R) × R |
          dist ((T : X → X)^[j] p.2.val) ((T : X → X)^[j] p.1.1.val) ≤ δ ∧
          dist ((T.symm : X → X)^[j] p.2.val) ((T.symm : X → X)^[j] p.1.2.val) ≤ δ} := by
      ext p
      constructor
      · intro hp
        have equal : bracket p.1 = p.2 := hp
        apply mem_iInter.mpr
        intro j
        change _ ∧ _
        rw [← equal]
        exact bounds p.1 j
      · intro hp
        exact unique p.1 p.2 (fun j => mem_iInter.mp hp j)
    rw [identity]
    apply isClosed_iInter
    intro j
    have actual : Continuous (fun p : (R × R) × R => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have first : Continuous (fun p : (R × R) × R => p.1.1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have second : Continuous (fun p : (R × R) × R => p.1.2.val) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
    exact (isClosed_le (((T.continuous.iterate j).comp actual).dist
      ((T.continuous.iterate j).comp first)) continuous_const).inter
        (isClosed_le (((T.symm.continuous.iterate j).comp actual).dist
          ((T.symm.continuous.iterate j).comp second)) continuous_const)
  refine ⟨bracket, continuous_of_isClosed_graph graph, bounds, ?_, ?_⟩
  · intro x
    apply unique
    intro j
    simp only [dist_self]
    exact ⟨positiveδ.le, positiveδ.le⟩
  · intro x y u v
    apply Subtype.ext
    apply expansive
    intro j
    have outer := bounds (bracket (x, y), bracket (u, v)) j
    have left := bounds (x, y) j
    have right := bounds (u, v) j
    have target := bounds (x, v) j
    constructor
    · have reverse := target.1
      rw [dist_comm] at reverse
      have firstTriangle := dist_triangle
        ((T : X → X)^[j] (bracket (bracket (x, y), bracket (u, v))).val)
        ((T : X → X)^[j] (bracket (x, y)).val) ((T : X → X)^[j] x.val)
      have secondTriangle := dist_triangle
        ((T : X → X)^[j] (bracket (bracket (x, y), bracket (u, v))).val)
        ((T : X → X)^[j] x.val) ((T : X → X)^[j] (bracket (x, v)).val)
      linarith
    · have reverse := target.2
      rw [dist_comm] at reverse
      have firstTriangle := dist_triangle
        ((T.symm : X → X)^[j] (bracket (bracket (x, y), bracket (u, v))).val)
        ((T.symm : X → X)^[j] (bracket (u, v)).val) ((T.symm : X → X)^[j] v.val)
      have secondTriangle := dist_triangle
        ((T.symm : X → X)^[j] (bracket (bracket (x, y), bracket (u, v))).val)
        ((T.symm : X → X)^[j] v.val) ((T.symm : X → X)^[j] (bracket (x, v)).val)
      linarith

end LeanShared.ExpansiveLocalProduct

namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions ExpansiveLocalProduct
open scoped Topology Manifold ContDiff

/-- The actual finite rectangle cover has continuous brackets satisfying
the full rectangular-band identity at every requested scale. -/
theorem BasicData.exists_finite_rectangle_brackets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ δ > 0, δ < ε ∧ ∃ N : ℕ, ∃ rectangles : Fin N → Set Λ,
      (⋃ i, rectangles i) = univ ∧ ∀ i,
        IsCompact (rectangles i) ∧
        (∀ x ∈ rectangles i, ∀ y ∈ rectangles i, dist x y ≤ δ) ∧
        ∃ bracket : rectangles i × rectangles i → rectangles i, Continuous bracket ∧
          (∀ p, ProductRelation (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant)
            δ p.1.val p.2.val (bracket p).val) ∧
          (∀ x : rectangles i, bracket (x, x) = x) ∧
          ∀ x y u v : rectangles i,
            bracket (bracket (x, y), bracket (u, v)) = bracket (x, v) := by
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
    b.exists_finite_small_rectangles forward inverse scale positiveScale
  have small : 3 * δ ≤ c := by
    have bound : scale ≤ c / 4 := min_le_right _ _
    linarith
  refine ⟨δ, positiveδ, smaller.trans_le (min_le_left _ _), N, rectangles, cover, ?_⟩
  intro i
  refine ⟨(properties i).1, (properties i).2.1, ?_⟩
  exact exists_continuous_rectangle_bracket S c δ (rectangles i) (properties i).1
    positiveδ expansiveS small (properties i).2.2

end LeanShared.HyperbolicBasicSet
