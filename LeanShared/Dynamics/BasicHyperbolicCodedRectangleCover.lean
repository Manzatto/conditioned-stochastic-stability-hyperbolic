module

public import LeanShared.Dynamics.FiniteSymbolicWeakTransitions
public import LeanShared.Dynamics.BasicHyperbolicFiniteSymbolicCoding

/-! The actual coded initial rectangle cover, with its finite graph,
surjective semiconjugacy and weak forward/backward transition inclusions
retained together.  This is the literal provenance needed for the final
Markov refinement; no transition field is supplied by a caller.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Function ThermodynamicDefinitions
open BilateralShadowingCoding
open scoped Topology Manifold ContDiff

/-- Actual hyperbolic data produce a literal finite coded rectangle cover
with both weak Markov inclusions on every chosen symbolic branch. -/
theorem BasicData.exists_coded_rectangle_cover
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
    ∃ τ > 0, τ < ε ∧ ∃ N : ℕ, ∃ R : Fin N → Fin N → Prop, ∃ center : Fin N → Λ,
      ∃ code : Path R → Λ, Continuous code ∧ Surjective code ∧
        (∀ a n, dist (BilateralHomeomorphismOrbit.orbit S (code a) n) (center (a.val (-n))) ≤ τ) ∧
        (∀ a, code (shift R a) = S (code a)) ∧
        (⋃ i, rectangle code i) = univ ∧
        (∀ i, IsCompact (rectangle code i) ∧
          ∀ x ∈ rectangle code i, ∀ y ∈ rectangle code i, dist x y ≤ 2 * τ) ∧
        ∀ a : Path R,
          (∀ y ∈ rectangle code (a.val 0),
            (∀ j : ℕ, dist ((S : Λ → Λ)^[j] y) ((S : Λ → Λ)^[j] (code a)) ≤ 2 * τ) →
              S y ∈ rectangle code (a.val 1) ∧
                ∀ j : ℕ, dist ((S : Λ → Λ)^[j] (S y)) ((S : Λ → Λ)^[j] (S (code a))) ≤ 2 * τ) ∧
          (∀ y ∈ rectangle code (a.val 1),
            (∀ j : ℕ, dist ((S.symm : Λ → Λ)^[j] y) ((S.symm : Λ → Λ)^[j] (S (code a))) ≤ 2 * τ) →
              S.symm y ∈ rectangle code (a.val 0) ∧
                ∀ j : ℕ, dist ((S.symm : Λ → Λ)^[j] (S.symm y)) ((S.symm : Λ → Λ)^[j] (code a)) ≤ 2 * τ) := by
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
  let τ := min (ε / 4) (c / 8)
  have positiveτ : 0 < τ := lt_min (by positivity) (by positivity)
  have scale : τ < ε := by have bound : τ ≤ ε / 4 := min_le_left _ _; linarith
  have small : 4 * τ ≤ c := by have bound : τ ≤ c / 8 := min_le_right _ _; linarith
  obtain ⟨N, R, center, code, continuous, onto, near, ambientIntertwines⟩ :=
    b.exists_finite_symbolic_coding forward inverse τ positiveτ
  have intertwines (a : Path R) : code (shift R a) = S (code a) :=
    Subtype.ext (ambientIntertwines a)
  refine ⟨τ, positiveτ, scale, N, R, center, code, continuous, onto, near, intertwines,
    rectangle_cover code onto, ?_, ?_⟩
  · intro i
    exact ⟨rectangle_compact code continuous i,
      fun x hx y hy => rectangle_diameter S center code τ near i x y hx hy⟩
  · intro a
    exact ⟨fun y inside stable => weak_stable_transition S center code c τ positiveτ.le
        expansiveS small near intertwines a y inside stable,
      fun y inside unstable => weak_unstable_transition S center code c τ positiveτ.le
        expansiveS small near intertwines a y inside unstable⟩

end LeanShared.HyperbolicBasicSet
