module

public import LeanShared.Dynamics.BilateralShadowingCoding
public import LeanShared.Dynamics.BasicHyperbolicShadowing
public import LeanShared.Dynamics.HyperbolicExpansivity
public import LeanShared.Dynamics.InvariantCoreHomeomorphism
public import LeanShared.Dynamics.PressureInvariantSubtype

/-! The actual compact hyperbolic core has a continuous surjective
finite-graph shadowing coding at every scale.  Both expansivity and
shadowing are derived from the literal basic data.  The fibers of this
prepartition coding are not asserted to be finite; Markov refinement and
signed periodic corrections remain further steps.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Function
open BilateralHomeomorphismOrbit BilateralShadowingCoding ThermodynamicDefinitions
open scoped Topology Manifold ContDiff

theorem BasicData.exists_finite_symbolic_coding
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ N : ℕ, ∃ R : Fin N → Fin N → Prop, ∃ center : Fin N → Λ,
      ∃ code : Path R → Λ, Continuous code ∧ Surjective code ∧
        (∀ a n, dist
          (BilateralHomeomorphismOrbit.orbit
            (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant) (code a) n)
          (center (a.val (-n))) ≤ ε) ∧
        ∀ a, (code (shift R a)).val = T (code a).val := by
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
  let δ := min ε (c / 3)
  have positiveδ : 0 < δ := lt_min positiveε (by positivity)
  have small : 2 * δ ≤ c := by
    have bound : δ ≤ c / 3 := min_le_right _ _
    linarith
  obtain ⟨η, positiveη, shadows⟩ := b.bilateral_shadowing forward
    (inverse.mdifferentiable one_ne_zero) δ positiveδ
  have shadowing : ∃ η > 0, ∀ reference : ℤ → Λ,
      (∀ n, dist (S (reference (n + 1))) (reference n) < η) →
      ∃ q : ℤ → Λ, (∀ n, S (q (n + 1)) = q n) ∧
        ∀ n, dist (q n) (reference n) < δ := by
    refine ⟨η, positiveη, fun reference pseudo => ?_⟩
    obtain ⟨q, qStep, qClose⟩ := shadows reference pseudo
    exact ⟨q, fun n => Subtype.ext (qStep n), qClose⟩
  obtain ⟨N, R, center, code, continuous, onto, near, intertwines⟩ :=
    exists_finite_coding S c δ positiveδ expansiveS small shadowing
  refine ⟨N, R, center, code, continuous, onto, ?_, ?_⟩
  · intro a n
    exact (near a n).trans (min_le_left _ _)
  · intro a
    exact congrArg Subtype.val (intertwines a)

end LeanShared.HyperbolicBasicSet
