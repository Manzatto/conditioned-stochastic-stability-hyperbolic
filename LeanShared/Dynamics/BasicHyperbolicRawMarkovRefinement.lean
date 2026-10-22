module

public import LeanShared.Dynamics.FiniteSymbolicCodedBracketRefinement
public import LeanShared.Dynamics.BasicHyperbolicCodedRectangleCover

/-! The raw finite classifier refinement of the literal hyperbolic
shadowing coding, with its proved forward stable Markov inclusion.
This retains the coding provenance needed to regularize the refinement
and establish the two-sided proper Markov partition.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Function ThermodynamicDefinitions
open BilateralShadowingCoding ExpansiveLocalProduct FiniteClosedRefinement
open scoped Topology Manifold ContDiff

/-- Actual basic data, with no supplied dynamical partition, produce
finite raw atoms satisfying the forward stable Markov inclusion. -/
theorem BasicData.exists_raw_markov_refinement
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : ℝ) (positiveε : 0 < ε) :
    let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
    ∃ c > 0, ∃ τ > 0, τ < ε ∧ 6 * τ ≤ c ∧
      (∀ x y : Λ, (∀ n : ℕ,
        dist ((S : Λ → Λ)^[n] x) ((S : Λ → Λ)^[n] y) ≤ c ∧
        dist ((S.symm : Λ → Λ)^[n] x) ((S.symm : Λ → Λ)^[n] y) ≤ c) → x = y) ∧
      ∃ N : ℕ, ∃ R : Fin N → Fin N → Prop, ∃ center : Fin N → Λ,
      ∃ code : Path R → Λ, ∃ bracket : ∀ i : Fin N,
        rectangle code i × rectangle code i → rectangle code i,
      Continuous code ∧ Surjective code ∧
      (∀ a n, dist (BilateralHomeomorphismOrbit.orbit S (code a) n) (center (a.val (-n))) ≤ τ) ∧
      (∀ a, code (shift R a) = S (code a)) ∧
      (∀ i, IsCompact (rectangle code i)) ∧
      (∀ i, Continuous (bracket i)) ∧
      (∀ i p, ProductRelation S (2 * τ) p.1.val p.2.val (bracket i p).val) ∧
      (∀ i (x : rectangle code i), bracket i (x, x) = x) ∧
      (∀ i (x y u v : rectangle code i),
        bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v)) ∧
      (∀ k, IsClosed (codedClassifiers code bracket k)) ∧
      (⋃ status, atom (codedClassifiers code bracket) status) = univ ∧
      (∀ status, ∀ x ∈ atom (codedClassifiers code bracket) status,
        ∀ y ∈ atom (codedClassifiers code bracket) status, dist x y ≤ 2 * τ) ∧
      (⋃ status, closure (interior (atom (codedClassifiers code bracket) status))) = univ ∧
      ∀ source target x y,
        x ∈ atom (codedClassifiers code bracket) source →
        y ∈ atom (codedClassifiers code bracket) source →
        S x ∈ atom (codedClassifiers code bracket) target →
        (∀ n : ℕ, dist ((S : Λ → Λ)^[n] y) ((S : Λ → Λ)^[n] x) ≤ 2 * τ) →
        S y ∈ atom (codedClassifiers code bracket) target ∧
          ∀ n : ℕ, dist ((S : Λ → Λ)^[n] (S y)) ((S : Λ → Λ)^[n] (S x)) ≤ 2 * τ := by
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  have forwardS (x : Λ) : (S x).val = T x.val := rfl
  have backwardS (x : Λ) : (S.symm x).val = T.symm x.val := rfl
  obtain ⟨c, positiveC, expansive⟩ := b.exists_expansivity_radius forward inverse
  have expansiveS : ∀ x y : Λ, (∀ n : ℕ,
      dist ((S : Λ → Λ)^[n] x) ((S : Λ → Λ)^[n] y) ≤ c ∧
      dist ((S.symm : Λ → Λ)^[n] x) ((S.symm : Λ → Λ)^[n] y) ≤ c) → x = y := by
    intro x y close
    apply Subtype.ext
    apply expansive x.val x.property y.val y.property
    intro n
    have estimate := close n
    change dist (((S : Λ → Λ)^[n] x).val) (((S : Λ → Λ)^[n] y).val) ≤ c ∧
      dist (((S.symm : Λ → Λ)^[n] x).val) (((S.symm : Λ → Λ)^[n] y).val) ≤ c at estimate
    simpa only [iterate_coe_restriction S forwardS, iterate_coe_restriction S.symm backwardS]
      using estimate
  let scale := min ε (c / 8)
  obtain ⟨τ, positiveτ, scaleBound, N, R, center, code, continuousCode, onto, near,
      intertwines, _baseCover, cylinders, _weakTransitions⟩ :=
    b.exists_coded_rectangle_cover forward inverse scale (lt_min positiveε (by positivity))
  have small : 6 * τ ≤ c := by
    have bound : scale ≤ c / 8 := min_le_right _ _
    linarith
  obtain ⟨bracket, continuousBracket, bounds, idempotent, band⟩ :=
    exists_coded_brackets S center code continuousCode c τ positiveτ expansiveS small near
  have compact (i : Fin N) : IsCompact (rectangle code i) := (cylinders i).1
  have closed := codedClassifiers_isClosed code bracket compact continuousBracket idempotent band
  refine ⟨c, positiveC, τ, positiveτ, scaleBound.trans_le (min_le_left _ _), small, expansiveS,
    N, R, center, code, bracket, continuousCode, onto, near, intertwines, compact,
    continuousBracket, bounds, idempotent, band, closed, atom_cover _, ?_,
    regularized_cover _ closed, ?_⟩
  · intro status
    exact codedAtom_small code onto bracket (2 * τ) (fun i => (cylinders i).2) status
  · intro source target x y hx hy imageX stable
    exact raw_atom_stable_forward S center code c τ positiveτ.le expansiveS (by linarith)
      near intertwines bracket bounds idempotent band source target x y hx hy imageX stable

end LeanShared.HyperbolicBasicSet
