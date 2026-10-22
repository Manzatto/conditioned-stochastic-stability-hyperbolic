module

public import LeanShared.Dynamics.BasicHyperbolicFiniteSymbolicCoding
import Mathlib.Tactic.Linarith

/-! The zero-coordinate images of an actual finite-graph shadowing code
form a compact cover by small rectangles.  Splicing admissible pasts and
futures proves the local stable/unstable product property.  These are the
initial rectangles, before the Markov refinement and multiplicity theorem.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit
open scoped Topology
variable {A X : Type*} [MetricSpace X]
  {R : A → A → Prop}

/-- The image of the zero-coordinate cylinder under a symbolic code. -/
@[expose] def rectangle (code : Path R → X) (i : A) : Set X :=
  code '' {a | a.val 0 = i}

theorem rectangle_compact [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] (code : Path R → X)
    (continuous : Continuous code) (i : A) : IsCompact (rectangle code i) := by
  have evaluation : Continuous (fun a : Path R => a.val 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have closed : IsClosed {a : Path R | a.val 0 = i} := isClosed_eq evaluation continuous_const
  exact closed.isCompact.image continuous

omit [MetricSpace X] in
theorem rectangle_cover (code : Path R → X) (onto : Surjective code) :
    (⋃ i : A, rectangle code i) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨a, rfl⟩ := onto x
  exact mem_iUnion.mpr ⟨a.val 0, ⟨a, rfl, rfl⟩⟩

theorem rectangle_diameter (T : X ≃ₜ X) (center : A → X) (code : Path R → X) (ε : ℝ)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (i : A) (x y : X) (hx : x ∈ rectangle code i) (hy : y ∈ rectangle code i) :
    dist x y ≤ 2 * ε := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have first := near a 0
  have second := near b 0
  simp only [zero, neg_zero] at first second
  rw [ha] at first
  rw [hb, dist_comm] at second
  linarith [dist_triangle (code a) (center i) (code b)]

/-- Concatenate a past and a future with the same zero symbol. -/
@[expose] def splice (a b : Path R) (same : a.val 0 = b.val 0) : Path R :=
  ⟨fun n => if n ≤ 0 then a.val n else b.val n, by
    intro n
    by_cases left : n ≤ 0
    · by_cases next : n + 1 ≤ 0
      · simpa only [ite_eq_left left, ite_eq_left next] using a.property n
      · have atZero : n = 0 := by omega
        subst n
        simp only [ite_eq_left le_rfl, show ¬(0 + 1 : ℤ) ≤ 0 from by omega, ite_false]
        rw [same]
        exact b.property 0
    · have next : ¬n + 1 ≤ 0 := by omega
      simpa only [ite_eq_right left, ite_eq_right next] using b.property n⟩

theorem splice_nonpos (a b : Path R) (same : a.val 0 = b.val 0)
    (n : ℤ) (nonpositive : n ≤ 0) : (splice a b same).val n = a.val n := by
  simp only [splice, ite_eq_left nonpositive]

theorem splice_nonneg (a b : Path R) (same : a.val 0 = b.val 0)
    (n : ℤ) (nonnegative : 0 ≤ n) : (splice a b same).val n = b.val n := by
  by_cases atZero : n = 0
  · subst n
    simpa only [splice, ite_eq_left le_rfl] using same
  · have positive : ¬n ≤ 0 := by omega
    simp only [splice, ite_eq_right positive]

theorem splice_future (T : X ≃ₜ X) (center : A → X) (code : Path R → X) (ε : ℝ)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (a b : Path R) (same : a.val 0 = b.val 0) (j : ℕ) :
    dist ((T : X → X)^[j] (code (splice a b same))) ((T : X → X)^[j] (code b)) ≤ 2 * ε := by
  have first := near (splice a b same) (-(j : ℤ))
  have second := near b (-(j : ℤ))
  simp only [neg_nat_time, neg_neg, splice_nonneg a b same (j : ℤ) (by omega)] at first second
  rw [dist_comm] at second
  linarith [dist_triangle ((T : X → X)^[j] (code (splice a b same)))
    (center (b.val (j : ℤ))) ((T : X → X)^[j] (code b))]

theorem splice_past (T : X ≃ₜ X) (center : A → X) (code : Path R → X) (ε : ℝ)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (a b : Path R) (same : a.val 0 = b.val 0) (j : ℕ) :
    dist ((T.symm : X → X)^[j] (code (splice a b same)))
      ((T.symm : X → X)^[j] (code a)) ≤ 2 * ε := by
  have first := near (splice a b same) (j : ℤ)
  have second := near a (j : ℤ)
  simp only [nat_time, splice_nonpos a b same (-(j : ℤ)) (by omega)] at first second
  rw [dist_comm] at second
  linarith [dist_triangle ((T.symm : X → X)^[j] (code (splice a b same)))
    (center (a.val (-(j : ℤ)))) ((T.symm : X → X)^[j] (code a))]

/-- The initial rectangles are closed under their local stable/unstable product. -/
theorem rectangle_product (T : X ≃ₜ X) (center : A → X) (code : Path R → X) (ε : ℝ)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (i : A) (x y : X) (hx : x ∈ rectangle code i) (hy : y ∈ rectangle code i) :
    ∃ z ∈ rectangle code i, ∀ j : ℕ,
      dist ((T : X → X)^[j] z) ((T : X → X)^[j] x) ≤ 2 * ε ∧
      dist ((T.symm : X → X)^[j] z) ((T.symm : X → X)^[j] y) ≤ 2 * ε := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  let same : b.val 0 = a.val 0 := hb.trans ha.symm
  refine ⟨code (splice b a same), ?_, fun j => ?_⟩
  · exact ⟨splice b a same, (splice_nonpos b a same 0 le_rfl).trans hb, rfl⟩
  · exact ⟨splice_future T center code ε near b a same j,
      splice_past T center code ε near b a same j⟩

/-- Expansivity makes the rectangle product independent of all coding choices. -/
theorem rectangle_product_unique (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
    (c ε : ℝ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (i : A) (x y : X) (hx : x ∈ rectangle code i) (hy : y ∈ rectangle code i) :
    ∃! z : X, z ∈ rectangle code i ∧ ∀ j : ℕ,
      dist ((T : X → X)^[j] z) ((T : X → X)^[j] x) ≤ 2 * ε ∧
      dist ((T.symm : X → X)^[j] z) ((T.symm : X → X)^[j] y) ≤ 2 * ε := by
  obtain ⟨z, inside, close⟩ := rectangle_product T center code ε near i x y hx hy
  refine ⟨z, ⟨inside, close⟩, fun w hw => ?_⟩
  apply expansive w z
  intro j
  have first := hw.2 j
  have second := close j
  constructor
  · have reverse := second.1
    rw [dist_comm] at reverse
    linarith [dist_triangle ((T : X → X)^[j] w) ((T : X → X)^[j] x)
      ((T : X → X)^[j] z)]
  · have reverse := second.2
    rw [dist_comm] at reverse
    linarith [dist_triangle ((T.symm : X → X)^[j] w) ((T.symm : X → X)^[j] y)
      ((T.symm : X → X)^[j] z)]

end LeanShared.BilateralShadowingCoding

namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Function ThermodynamicDefinitions BilateralShadowingCoding
open scoped Topology Manifold ContDiff

/-- Actual compact hyperbolic data produce an arbitrarily small finite
cover by compact rectangles with a unique local stable/unstable product. -/
theorem BasicData.exists_finite_small_rectangles
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
        ∀ x ∈ rectangles i, ∀ y ∈ rectangles i, ∃! z : Λ,
          z ∈ rectangles i ∧ ∀ j : ℕ,
            dist (((invariantCoreHomeomorphism T Λ b.hyperbolic.invariant : Λ → Λ)^[j]) z)
              (((invariantCoreHomeomorphism T Λ b.hyperbolic.invariant : Λ → Λ)^[j]) x) ≤ δ ∧
            dist ((((invariantCoreHomeomorphism T Λ b.hyperbolic.invariant).symm : Λ → Λ)^[j]) z)
              ((((invariantCoreHomeomorphism T Λ b.hyperbolic.invariant).symm : Λ → Λ)^[j]) y) ≤ δ := by
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
  let α := min (ε / 4) (c / 8)
  have positiveα : 0 < α := lt_min (by positivity) (by positivity)
  have small : 4 * α ≤ c := by
    have bound : α ≤ c / 8 := min_le_right _ _
    linarith
  have diameterSmall : 2 * α < ε := by
    have bound : α ≤ ε / 4 := min_le_left _ _
    linarith
  obtain ⟨N, R, center, code, continuous, onto, near, _intertwines⟩ :=
    b.exists_finite_symbolic_coding forward inverse α positiveα
  refine ⟨2 * α, by positivity, diameterSmall, N, rectangle code, rectangle_cover code onto, ?_⟩
  intro i
  refine ⟨rectangle_compact code continuous i, ?_, ?_⟩
  · exact fun x hx y hy => rectangle_diameter S center code α near i x y hx hy
  · exact fun x hx y hy => rectangle_product_unique S center code c α expansiveS small near i x y hx hy

end LeanShared.HyperbolicBasicSet
