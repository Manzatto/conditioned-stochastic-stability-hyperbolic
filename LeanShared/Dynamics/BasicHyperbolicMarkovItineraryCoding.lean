module

public import LeanShared.Dynamics.BasicHyperbolicRawMarkovRefinement
public import LeanShared.Dynamics.MarkovItineraryCoding

/-! Actual hyperbolic basic data construct the refined transition graph
and its continuous surjective itinerary coding.  The original finite
graph, shadowing code and cylinder brackets are retained, as is membership
in every closed finite raw-atom itinerary cylinder.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Function ThermodynamicDefinitions
open BilateralShadowingCoding ExpansiveLocalProduct FiniteClosedRefinement MarkovFinitePathRealization
open scoped Topology Manifold ContDiff

theorem BasicData.exists_markov_itinerary_coding
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
      ∃ initialCode : Path R → Λ, ∃ bracket : ∀ i : Fin N,
        rectangle initialCode i × rectangle initialCode i → rectangle initialCode i,
      Continuous initialCode ∧ Surjective initialCode ∧
      (∀ a n, dist (BilateralHomeomorphismOrbit.orbit S (initialCode a) n) (center (a.val (-n))) ≤ τ) ∧
      (∀ a, initialCode (shift R a) = S (initialCode a)) ∧
      (∀ i p, ProductRelation S (2 * τ) p.1.val p.2.val (bracket i p).val) ∧
      (∀ i (x : rectangle initialCode i), bracket i (x, x) = x) ∧
      (∀ i (x y u v : rectangle initialCode i),
        bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v)) ∧
      let atoms := fun status => atom (codedClassifiers initialCode bracket) status
      ∃ code : Path (Transition S atoms) → Λ,
        Continuous code ∧ Surjective code ∧
        (∀ a, code (shift (Transition S atoms) a) = S (code a)) ∧
        ∀ a radius, code a ∈ closure (itineraryWindow S atoms a.val radius) := by
  classical
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  obtain ⟨c, positiveC, τ, positiveτ, smaller, small, expansive,
    N, R, center, initialCode, bracket, continuousInitial, onto, nearInitial, intertwinesInitial,
    _compact, _continuousBracket, bounds, idempotent, band, _closed, cover, diameter,
    _regularizedCover, _forwardRaw⟩ := b.exists_raw_markov_refinement forward inverse ε positiveε
  let I := (Fin N ⊕ ((Fin N × Fin N) × Bool)) → Bool
  let atoms : I → Set Λ := fun status => atom (codedClassifiers initialCode bracket) status
  have defaultPoint : Nonempty Λ := Set.nonempty_coe_sort.mpr b.nonempty
  let default : Λ := Classical.choice defaultPoint
  let refinedCenter : I → Λ := fun status =>
    if h : (atoms status).Nonempty then Classical.choose h else default
  have nearCenter (status : I) (x : Λ) (hx : x ∈ atoms status) :
      dist x (refinedCenter status) ≤ 2 * τ := by
    have nonempty : (atoms status).Nonempty := ⟨x, hx⟩
    have centerInside : refinedCenter status ∈ atoms status := by
      simp only [refinedCenter, dite_eq_left nonempty]
      exact Classical.choose_spec nonempty
    exact diameter status x hx _ centerInside
  have realized (word : ℕ → I) (length : ℕ) (initial : (atoms (word 0)).Nonempty)
      (edges : ∀ k < length, Transition S atoms (word k) (word (k + 1))) :
      ∃ x : Λ, ∀ k ≤ length, (S : Λ → Λ)^[k] x ∈ atoms (word k) :=
    codedAtom_finite_path_realized S center initialCode onto c τ positiveτ.le expansive (by linarith)
      nearInitial intertwinesInitial bracket bounds idempotent band word length initial edges
  obtain ⟨code, continuousCode, codeOnto, _nearCode, codeIntertwines, windows⟩ :=
    exists_itinerary_coding S atoms refinedCenter c (2 * τ) expansive (by linarith) cover nearCenter realized
  exact ⟨c, positiveC, τ, positiveτ, smaller, small, expansive, N, R, center, initialCode, bracket,
    continuousInitial, onto, nearInitial, intertwinesInitial, bounds, idempotent, band,
    code, continuousCode, codeOnto, codeIntertwines, windows⟩

end LeanShared.HyperbolicBasicSet
