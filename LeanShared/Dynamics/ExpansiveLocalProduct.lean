module

public import LeanShared.Dynamics.BasicHyperbolicFiniteSymbolicCoding
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.Linarith

/-! A continuous local stable/unstable product is constructed by pasting
two actual orbits, shadowing the single jump, and using expansivity for
uniqueness.  The actual hyperbolic specialization assumes no bracket map.
-/

public noncomputable section
namespace LeanShared.ExpansiveLocalProduct
open Set Function BilateralHomeomorphismOrbit
open scoped Topology
variable {X : Type*} [MetricSpace X]

/-- A point in the local stable set of `x` and local unstable set of `y`. -/
@[expose] def ProductRelation (T : X ≃ₜ X) (δ : ℝ) (x y z : X) : Prop :=
  ∀ j : ℕ, dist ((T : X → X)^[j] z) ((T : X → X)^[j] x) ≤ δ ∧
    dist ((T.symm : X → X)^[j] z) ((T.symm : X → X)^[j] y) ≤ δ

/-- The neighborhood of the diagonal on which the product is defined. -/
@[expose] def NearbyPairs (η : ℝ) := {p : X × X // dist p.1 p.2 < η}

instance (η : ℝ) : TopologicalSpace (NearbyPairs (X := X) η) := inferInstanceAs
  (TopologicalSpace {p : X × X // dist p.1 p.2 < η})

theorem product_unique (T : X ≃ₜ X) (c δ : ℝ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c) (x y z w : X)
    (hz : ProductRelation T δ x y z) (hw : ProductRelation T δ x y w) : z = w := by
  apply expansive z w
  intro j
  have first := hz j
  have second := hw j
  constructor
  · have reverse := second.1
    rw [dist_comm] at reverse
    linarith [dist_triangle ((T : X → X)^[j] z) ((T : X → X)^[j] x)
      ((T : X → X)^[j] w)]
  · have reverse := second.2
    rw [dist_comm] at reverse
    linarith [dist_triangle ((T.symm : X → X)^[j] z) ((T.symm : X → X)^[j] y)
      ((T.symm : X → X)^[j] w)]

/-- Compact expansive bilateral shadowing constructs a continuous local product. -/
theorem exists_continuous_local_product [CompactSpace X] (T : X ≃ₜ X) (c δ : ℝ)
    (positiveδ : 0 < δ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c)
    (shadowing : ∃ η > 0, ∀ reference : ℤ → X,
      (∀ n, dist (T (reference (n + 1))) (reference n) < η) →
      ∃ q : ℤ → X, (∀ n, T (q (n + 1)) = q n) ∧
        ∀ n, dist (q n) (reference n) < δ / 2) :
    ∃ η > 0, η ≤ δ / 2 ∧ ∃ bracket : NearbyPairs (X := X) η → X,
      Continuous bracket ∧
        (∀ p, ProductRelation T δ p.val.1 p.val.2 (bracket p)) ∧
        ∀ (x : X) (h : dist x x < η), bracket ⟨(x, x), h⟩ = x := by
  obtain ⟨η₀, positiveη₀, shadows⟩ := shadowing
  let η := min η₀ (δ / 2)
  have positiveη : 0 < η := lt_min positiveη₀ (by positivity)
  have radiusSmall : η ≤ δ / 2 := min_le_right _ _
  have shadowExists (p : NearbyPairs (X := X) η) :
      ∃ z : X, ProductRelation T δ p.val.1 p.val.2 z := by
    let reference : ℤ → X := fun n =>
      if n ≤ 0 then orbit T p.val.1 n else orbit T p.val.2 n
    have pseudo (n : ℤ) : dist (T (reference (n + 1))) (reference n) < η₀ := by
      by_cases left : n ≤ 0
      · by_cases next : n + 1 ≤ 0
        · simpa only [reference, ite_eq_left left, ite_eq_left next, step, dist_self]
            using positiveη₀
        · have atZero : n = 0 := by omega
          subst n
          simp only [reference, ite_eq_left le_rfl,
            show ¬(0 + 1 : ℤ) ≤ 0 from by omega, ite_false, step, zero]
          rw [dist_comm]
          exact p.property.trans_le (min_le_left _ _)
      · have next : ¬n + 1 ≤ 0 := by omega
        simpa only [reference, ite_eq_right left, ite_eq_right next, step, dist_self]
          using positiveη₀
    obtain ⟨q, qStep, qClose⟩ := shadows reference pseudo
    have canonical := eq_canonical T q qStep
    refine ⟨q 0, fun j => ?_⟩
    constructor
    · have estimate := qClose (-(j : ℤ))
      rw [congrFun canonical (-(j : ℤ)), neg_nat_time] at estimate
      have nonpositive : -(j : ℤ) ≤ 0 := by omega
      simp only [reference, ite_eq_left nonpositive, neg_nat_time] at estimate
      linarith
    · by_cases atZero : j = 0
      · subst j
        have estimate := qClose 0
        simp only [reference, ite_eq_left le_rfl, zero] at estimate
        have nearby := p.property
        have triangle := dist_triangle (q 0) p.val.1 p.val.2
        simp only [Function.iterate_zero_apply]
        linarith
      · have positive : ¬(j : ℤ) ≤ 0 :=
          not_le.mpr (by exact_mod_cast Nat.pos_of_ne_zero atZero)
        have estimate := qClose (j : ℤ)
        rw [congrFun canonical (j : ℤ), nat_time] at estimate
        simp only [reference, ite_eq_right positive, nat_time] at estimate
        linarith
  choose bracket bounds using shadowExists
  have unique (p : NearbyPairs (X := X) η) (z : X)
      (hz : ProductRelation T δ p.val.1 p.val.2 z) : bracket p = z :=
    product_unique T c δ expansive small _ _ _ _ (bounds p) hz
  have graph : IsClosed bracket.graph := by
    have identity : bracket.graph = ⋂ j : ℕ,
        {p : NearbyPairs (X := X) η × X |
          dist ((T : X → X)^[j] p.2) ((T : X → X)^[j] p.1.val.1) ≤ δ ∧
          dist ((T.symm : X → X)^[j] p.2) ((T.symm : X → X)^[j] p.1.val.2) ≤ δ} := by
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
    have first : Continuous (fun p : NearbyPairs (X := X) η × X => p.1.val.1) :=
      continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
    have second : Continuous (fun p : NearbyPairs (X := X) η × X => p.1.val.2) :=
      continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
    exact (isClosed_le (((T.continuous.iterate j).comp continuous_snd).dist
      ((T.continuous.iterate j).comp first)) continuous_const).inter
        (isClosed_le (((T.symm.continuous.iterate j).comp continuous_snd).dist
          ((T.symm.continuous.iterate j).comp second)) continuous_const)
  refine ⟨η, positiveη, radiusSmall, bracket, continuous_of_isClosed_graph graph, bounds, ?_⟩
  intro x h
  apply unique
  intro j
  simp only [dist_self]
  exact ⟨positiveδ.le, positiveδ.le⟩

end LeanShared.ExpansiveLocalProduct

namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions ExpansiveLocalProduct
open scoped Topology Manifold ContDiff

/-- The actual locally maximal hyperbolic core has a continuous local
product on a neighborhood of the diagonal at every requested scale. -/
theorem BasicData.exists_continuous_local_product
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ δ > 0, δ < ε ∧ ∃ η > 0, η ≤ δ / 2 ∧
      ∃ bracket : NearbyPairs (X := Λ) η → Λ, Continuous bracket ∧
        (∀ p, ProductRelation (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant)
          δ p.val.1 p.val.2 (bracket p)) ∧
        ∀ (x : Λ) (h : dist x x < η), bracket ⟨(x, x), h⟩ = x := by
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
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
  let δ := min (ε / 2) (c / 3)
  have positiveδ : 0 < δ := lt_min (by positivity) (by positivity)
  have small : 2 * δ ≤ c := by
    have bound : δ ≤ c / 3 := min_le_right _ _
    linarith
  have scale : δ < ε := by
    have bound : δ ≤ ε / 2 := min_le_left _ _
    linarith
  obtain ⟨η₀, positiveη₀, shadows⟩ := b.bilateral_shadowing forward
    (inverse.mdifferentiable one_ne_zero) (δ / 2) (by positivity)
  have shadowing : ∃ η > 0, ∀ reference : ℤ → Λ,
      (∀ n, dist (S (reference (n + 1))) (reference n) < η) →
      ∃ q : ℤ → Λ, (∀ n, S (q (n + 1)) = q n) ∧
        ∀ n, dist (q n) (reference n) < δ / 2 := by
    refine ⟨η₀, positiveη₀, fun reference pseudo => ?_⟩
    obtain ⟨q, qStep, qClose⟩ := shadows reference pseudo
    exact ⟨q, fun n => Subtype.ext (qStep n), qClose⟩
  exact ⟨δ, positiveδ, scale,
    ExpansiveLocalProduct.exists_continuous_local_product S c δ positiveδ expansiveS small shadowing⟩

end LeanShared.HyperbolicBasicSet
