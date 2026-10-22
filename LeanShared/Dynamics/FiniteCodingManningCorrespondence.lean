module

public import LeanShared.Dynamics.FiniteCodingGeometry
public import LeanShared.Dynamics.PeriodicMatchingSignedCoefficient

/-! The exact Manning correspondence uses the derived finite coding
geometry, and therefore applies to the SAME primitive full-interior
coding as the Ruelle operator.  The original closed-classifier packet is
not required to falsely enumerate that pruned alphabet as a Boolean cube.
The original periodic fibers, matching paths and signs are unchanged.
-/

public noncomputable section
namespace LeanShared.FiniteCodingManning
open Set Function BilateralShadowingCoding MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A]

theorem matchingFiberSubset_injective (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : FiniteCodingGeometry T rectangles code) (k : ℕ) (x : X)
    (period : ℕ) (positive : 0 < period) (fixed : (T : X → X)^[period] x = x) :
    Injective (matchingFiberSubset T rectangles code properties.geometry k x) := by
  classical
  intro a b equal
  have sources : (a.val.val 0).val.1 = (b.val.val 0).val.1 := by
    apply Subtype.ext
    rw [matchingFiberSubset_source_labels T rectangles code properties.geometry k x a,
      matchingFiberSubset_source_labels T rectangles code properties.geometry k x b, equal]
  have coordinates (i : Fin (k + 1)) :
      matchingFiberCoordinate T rectangles code properties.geometry k x a i =
        matchingFiberCoordinate T rectangles code properties.geometry k x b i := by
    apply properties.periodicSymbols x period positive fixed 0
    change subsetSymbol (a.val.val 0).val.1 i = subsetSymbol (b.val.val 0).val.1 i
    rw [sources]
  apply Subtype.ext
  apply liftMatchingPath_injective
  apply Subtype.ext
  funext n i
  exact congrArg (fun p : code ⁻¹' {x} => p.val.val n) (coordinates i)


theorem matchingFiberSubset_tuple_projection (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : FiniteCodingGeometry T rectangles code)
    (x : X) [DecidableEq (code ⁻¹' {x})] (period : ℕ) (positive : 0 < period)
    (fixed : (T : X → X)^[period] x = x) (k : ℕ)
    (a : Path (FiberTupleTransition (Transition T rectangles) (Affiliated rectangles) (k + 1)))
    (lifts : Fin (k + 1) → code ⁻¹' {x})
    (coordinates : ∀ i, tupleCoordinate a i = (lifts i).val)
    (inside : matchingCode T rectangles code k (tupleToMatchingPath a) = x) :
    matchingFiberSubset T rectangles code properties.geometry k x ⟨tupleToMatchingPath a, inside⟩ =
      Finset.univ.image lifts := by
  classical
  apply Finset.image_injective (properties.periodicSymbols x period positive fixed 0)
  rw [← matchingFiberSubset_source_labels T rectangles code properties.geometry k x ⟨tupleToMatchingPath a, inside⟩]
  change Finset.univ.image (a.val 0) = (Finset.univ.image lifts).image (fun p : code ⁻¹' {x} => p.val.val 0)
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact congrArg (fun p : Path (Transition T rectangles) => p.val 0) (coordinates i)


theorem periodic_fiber_subset_matching_exact (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : FiniteCodingGeometry T rectangles code)
    (x : X) [DecidableEq (code ⁻¹' {x})] (period : ℕ) (positive : 0 < period)
    (fixed : (T : X → X)^[period] x = x)
    (P : Equiv.Perm (code ⁻¹' {x}))
    (returns : ∀ a, (P a).val = (shift (Transition T rectangles) : _ → _)^[period] a.val)
    (s : Finset (code ⁻¹' {x})) (invariant : ∀ a, P a ∈ s ↔ a ∈ s)
    (k : ℕ) (card : s.card = k + 1) :
    ∃ walk : Path (SubsetMatchingEdgeTransition (Transition T rectangles) (Affiliated rectangles) (k + 1)),
      ∃ inside : matchingCode T rectangles code k walk = x,
      matchingFiberSubset T rectangles code properties.geometry k x ⟨walk, inside⟩ = s ∧
      Function.Periodic walk.val (period : ℤ) ∧
      (∏ i ∈ Finset.range period, matchingEdgeSign (walk.val i)) = Equiv.Perm.sign (P.subtypePerm invariant) := by
  let enum : Fin (k + 1) ≃ s := (s.equivFinOfCardEq card).symm
  let lifts : Fin (k + 1) → code ⁻¹' {x} := fun i => (enum i).val
  have distinct : Injective lifts := Subtype.val_injective.comp enum.injective
  obtain ⟨a, coordinates⟩ := exists_periodic_fiber_tuple T rectangles code properties.intertwines
    properties.finiteFibers properties.geometry x period positive fixed (k + 1) lifts distinct
  let restriction := P.subtypePerm invariant
  let q : Equiv.Perm (Fin (k + 1)) := (enum.trans restriction).trans enum.symm
  have indexed (i : Fin (k + 1)) : lifts (q i) = P (lifts i) := by
    have identity := enum.apply_symm_apply (restriction (enum i))
    exact congrArg (fun z : s => z.val) identity
  have monodromy (j : ℤ) : a.val (j + period) = a.val j ∘ q := by
    funext i
    have first := congrArg (fun p : Path (Transition T rectangles) => p.val (j + period)) (coordinates i)
    have last := congrArg (fun p : Path (Transition T rectangles) => p.val j) (coordinates (q i))
    calc
      a.val (j + period) i = (lifts i).val.val (j + period) := first
      _ = ((shift (Transition T rectangles) : _ → _)^[period] (lifts i).val).val j :=
        (shift_iterate_val (lifts i).val period j).symm
      _ = (P (lifts i)).val.val j := congrArg
        (fun p : Path (Transition T rectangles) => p.val j) (returns (lifts i)).symm
      _ = (lifts (q i)).val.val j := by rw [indexed i]
      _ = a.val j (q i) := last.symm
  have inside : matchingCode T rectangles code k (tupleToMatchingPath a) = x := by
    rw [matchingCode_tuple_projection T rectangles code properties.geometry k a 0, coordinates 0]
    exact (lifts 0).property
  refine ⟨tupleToMatchingPath a, inside, ?_,
    tupleMatching_periodic_of_monodromy a period q monodromy, ?_⟩
  · rw [matchingFiberSubset_tuple_projection T rectangles code properties x period positive fixed k a lifts coordinates inside]
    ext p
    constructor
    · intro member
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
      exact (enum i).property
    · intro member
      refine Finset.mem_image.mpr ⟨enum.symm ⟨p, member⟩, Finset.mem_univ _, ?_⟩
      exact congrArg (fun z : s => z.val) (enum.apply_symm_apply ⟨p, member⟩)
  · rw [tupleMatching_sign_monodromy a period q monodromy]
    exact Equiv.Perm.sign_trans_trans_symm restriction enum


omit [DecidableEq A] in
theorem periodic_matching_fiber_subset (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : FiniteCodingGeometry T rectangles code) (k : ℕ) (x : X)
    [DecidableEq (code ⁻¹' {x})] (period : ℕ)
    (P : Equiv.Perm (code ⁻¹' {x}))
    (returns : ∀ a, (P a).val = (shift (Transition T rectangles) : _ → _)^[period] a.val)
    (a : (matchingCode T rectangles code k) ⁻¹' {x})
    (periodic : Function.Periodic a.val.val (period : ℤ)) :
    ∃ invariant : ∀ p, P p ∈ matchingFiberSubset T rectangles code properties.geometry k x a ↔
        p ∈ matchingFiberSubset T rectangles code properties.geometry k x a,
      (∏ i ∈ Finset.range period, matchingEdgeSign (a.val.val i)) =
        Equiv.Perm.sign (P.subtypePerm invariant) := by
  classical
  let c := matchingFiberCoordinate T rectangles code properties.geometry k x a
  let q := indexTransport (matchingPathPermutation a.val) period
  let s := matchingFiberSubset T rectangles code properties.geometry k x a
  have moves (i : Fin (k + 1)) : P (c i) = c (q i) := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    have monodromy := congrArg (fun u : Fin (k + 1) → A => u i)
      (matching_lift_monodromy a.val period periodic j)
    have returned := congrArg (fun p : Path (Transition T rectangles) => p.val j) (returns (c i))
    exact returned.trans ((shift_iterate_val (c i).val period j).trans monodromy)
  have invariant : ∀ p, P p ∈ s ↔ p ∈ s := by
    intro p
    constructor
    · intro inside
      obtain ⟨i, equal⟩ := (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a (P p)).mp inside
      have original : c (q.symm i) = p := P.injective
        ((moves (q.symm i)).trans (by simpa only [Equiv.apply_symm_apply] using equal))
      exact (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a p).mpr ⟨q.symm i, original⟩
    · intro inside
      obtain ⟨i, rfl⟩ := (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a p).mp inside
      exact (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a (P (c i))).mpr ⟨q i, (moves i).symm⟩
  let f : Fin (k + 1) → s := fun i => ⟨c i, (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a (c i)).mpr ⟨i, rfl⟩⟩
  have bijective : Bijective f := by
    constructor
    · intro i j equal
      exact matchingFiberCoordinate_injective T rectangles code properties.geometry k x a
        (congrArg (fun p : s => p.val) equal)
    · intro p
      obtain ⟨i, equal⟩ := (mem_matchingFiberSubset_iff T rectangles code properties.geometry k x a p.val).mp p.property
      exact ⟨i, Subtype.ext equal⟩
  let e := Equiv.ofBijective f bijective
  have conjugacy : P.subtypePerm invariant = (e.symm.trans q).trans e := by
    apply Equiv.ext
    intro p
    obtain ⟨i, rfl⟩ := e.surjective p
    apply Subtype.ext
    change P (c i) = c (q (e.symm (e i)))
    simpa only [Equiv.symm_apply_apply] using moves i
  refine ⟨invariant, ?_⟩
  rw [matching_path_sign_product, conjugacy]
  exact (Equiv.Perm.sign_symm_trans_trans q e).symm


theorem periodic_matching_all_subsets_equivalence (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : FiniteCodingGeometry T rectangles code)
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


theorem periodicMatchingSignedCoefficient_eq_one (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : FiniteCodingGeometry T rectangles code)
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
    (properties : FiniteCodingGeometry T rectangles code)
    (x : X) (period : ℕ) (positive : 0 < period) (fixed : (T : X → X)^[period] x = x) :
    Finite (Σ k : ℕ, PeriodicMatchingFiber T rectangles code k x period) := by
  classical
  let : Fintype (code ⁻¹' {x}) := (properties.finiteFibers x).fintype
  obtain ⟨P, returns⟩ := properties.returnPermutation x period fixed
  obtain ⟨e, _⟩ := periodic_matching_all_subsets_equivalence T rectangles code properties x period positive fixed P returns
  exact Finite.of_injective e e.injective


end LeanShared.FiniteCodingManning
