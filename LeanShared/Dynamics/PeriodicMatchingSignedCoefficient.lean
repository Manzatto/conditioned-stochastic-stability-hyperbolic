module

public import LeanShared.Dynamics.PeriodicMatchingSubsetEquivalence
public import LeanShared.Analysis.FinitePermutationInvariantFinsum
public import Mathlib.Tactic.Ring

/-! The actual signed periodic matching correction over each periodic
base point has coefficient exactly one.  All orders are indexed by a
sigma type; the constructed equivalence with nonempty invariant subsets
makes this an actual finite correction, without source-oracle fields.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A]

theorem periodic_matching_all_subsets_equivalence (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code)
    (x : X) [DecidableEq (code ⁻¹' {x})] (period : ℕ) (positive : 0 < period)
    (fixed : (T : X → X)^[period] x = x)
    (P : Equiv.Perm (code ⁻¹' {x}))
    (returns : ∀ a, (P a).val = (shift (Transition T rectangles) : _ → _)^[period] a.val) :
    ∃ e : (Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period) ≃
      {s : Finset (code ⁻¹' {x}) // s.Nonempty ∧ ∀ p, P p ∈ s ↔ p ∈ s},
      ∀ a, (e a).val = matchingFiberSubset T rectangles code properties.geometry a.1 x a.2.val ∧
        (∏ i ∈ Finset.range period, matchingEdgeSign (a.2.val.val.val i)) =
          Equiv.Perm.sign (P.subtypePerm (e a).property.2) := by
  classical
  let source := Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period
  let target := {s : Finset (code ⁻¹' {x}) // s.Nonempty ∧ ∀ p, P p ∈ s ↔ p ∈ s}
  have invariant (a : source) : ∀ p,
      P p ∈ matchingFiberSubset T rectangles code properties.geometry a.1 x a.2.val ↔
      p ∈ matchingFiberSubset T rectangles code properties.geometry a.1 x a.2.val :=
    (periodic_matching_fiber_subset T rectangles code properties a.1 x period P returns a.2.val a.2.property).choose
  have nonempty (a : source) :
      (matchingFiberSubset T rectangles code properties.geometry a.1 x a.2.val).Nonempty :=
    Finset.card_pos.mp (by rw [matchingFiberSubset_card]; omega)
  let f : source → target := fun a =>
    ⟨matchingFiberSubset T rectangles code properties.geometry a.1 x a.2.val, nonempty a, invariant a⟩
  have bijective : Bijective f := by
    constructor
    · rintro ⟨k, a⟩ ⟨l, b⟩ equal
      have subsets := congrArg (fun s : target => s.val) equal
      change matchingFiberSubset T rectangles code properties.geometry k x a.val =
        matchingFiberSubset T rectangles code properties.geometry l x b.val at subsets
      have lengths := congrArg Finset.card subsets
      simp only [matchingFiberSubset_card] at lengths
      have sameOrder : k = l := by omega
      subst l
      have sameWalk : a = b := by
        apply Subtype.ext
        exact matchingFiberSubset_injective T rectangles code properties k x period positive fixed subsets
      subst b
      rfl
    · intro s
      let k := s.val.card - 1
      have card : s.val.card = k + 1 := by have bound := s.property.1.card_pos; dsimp only [k]; omega
      obtain ⟨walk, inside, extracted, periodic, _sign⟩ :=
        periodic_fiber_subset_matching_exact T rectangles code properties x period positive fixed
          P returns s.val s.property.2 k card
      exact ⟨⟨k, ⟨⟨walk, inside⟩, periodic⟩⟩, Subtype.ext extracted⟩
  let e := Equiv.ofBijective f bijective
  refine ⟨e, fun a => ⟨rfl, ?_⟩⟩
  exact (periodic_matching_fiber_subset T rectangles code properties a.1 x period P returns a.2.val a.2.property).choose_spec

@[expose] def periodicMatchingSignedCoefficient (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (x : X) (period : ℕ) : ℚ :=
  ∑ᶠ a : (Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period),
    (-1 : ℚ) ^ a.1 * ((∏ i ∈ Finset.range period, matchingEdgeSign (a.2.val.val.val i)) : ℚ)

theorem periodicMatchingSignedCoefficient_eq_one (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code)
    (x : X) (period : ℕ) (positive : 0 < period) (fixed : (T : X → X)^[period] x = x) :
    periodicMatchingSignedCoefficient T rectangles code x period = 1 := by
  classical
  let : Fintype (code ⁻¹' {x}) := (properties.finiteFibers x).fintype
  obtain ⟨a, image⟩ := properties.onto x
  let : Nonempty (code ⁻¹' {x}) := ⟨⟨a, image⟩⟩
  obtain ⟨P0, returns⟩ := properties.returnPermutation x period fixed
  let P : Equiv.Perm (code ⁻¹' {x}) := P0
  obtain ⟨e, exactFiber⟩ := periodic_matching_all_subsets_equivalence T rectangles code properties
    x period positive fixed P returns
  unfold periodicMatchingSignedCoefficient
  calc
    _ = ∑ᶠ s : {s : Finset (code ⁻¹' {x}) // s.Nonempty ∧ ∀ p, P p ∈ s ↔ p ∈ s},
        -((-1 : ℚ) ^ s.val.card * (Equiv.Perm.sign (P.subtypePerm s.property.2) : ℚ)) := by
      apply finsum_eq_of_bijective e e.bijective
      intro b
      have length : (e b).val.card = b.1 + 1 := by
        rw [(exactFiber b).1, matchingFiberSubset_card]
      rw [length, ← (exactFiber b).2, pow_succ]
      push_cast
      ring
    _ = 1 := FinitePermutationMinorCancellation.finsum_nonempty_invariant_signed_sum P

theorem periodicMatchingFiberSigma_finite (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code)
    (x : X) (period : ℕ) (positive : 0 < period) (fixed : (T : X → X)^[period] x = x) :
    Finite (Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period) := by
  classical
  let : Fintype (code ⁻¹' {x}) := (properties.finiteFibers x).fintype
  obtain ⟨P, returns⟩ := properties.returnPermutation x period fixed
  obtain ⟨e, _⟩ := periodic_matching_all_subsets_equivalence T rectangles code properties x period positive fixed P returns
  exact Finite.of_injective e e.injective

omit [TopologicalSpace A] [DecidableEq A] in
theorem periodicMatching_order_bound (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (x : X) (period : ℕ)
    (a : Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period) : a.1 < Fintype.card A := by
  have estimate := Finset.card_le_univ (a.2.val.val.val 0).val.1.val
  rw [(a.2.val.val.val 0).val.1.property.1] at estimate
  omega

end LeanShared.BilateralShadowingCoding
