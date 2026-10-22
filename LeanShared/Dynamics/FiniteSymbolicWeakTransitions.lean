module

public import LeanShared.Dynamics.FiniteSymbolicRectangles
public import LeanShared.Dynamics.ExpansiveLocalProduct
import Mathlib.Tactic.Linarith

/-! Weak Markov transitions of the literal cylinder-image cover.  A
chosen coded branch fixes the next or previous symbol.  Splicing and
expansivity keep the entire corresponding stable or unstable slice in
that branch.  No dynamical inclusion is inferred from partition topology.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit ExpansiveLocalProduct
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X]
  {R : A → A → Prop}

@[simp] theorem shift_symm_apply (a : Path R) (n : ℤ) :
    ((shift R).symm a).val n = a.val (n - 1) := rfl

theorem code_shift_inverse (T : X ≃ₜ X) (code : Path R → X)
    (intertwines : ∀ a, code (shift R a) = T (code a)) (a : Path R) :
    code ((shift R).symm a) = T.symm (code a) := by
  apply T.injective
  rw [T.apply_symm_apply]
  exact (intertwines ((shift R).symm a)).symm.trans
    (congrArg code ((shift R).apply_symm_apply a))

/-- On a literal coded transition, the forward image of the local stable
slice in the first rectangle lies in the second cylinder-image rectangle. -/
theorem weak_stable_transition (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
    (c ε : ℝ) (nonnegativeε : 0 ≤ ε)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (intertwines : ∀ a, code (shift R a) = T (code a))
    (a : Path R) (y : X) (inside : y ∈ rectangle code (a.val 0))
    (stable : ∀ j : ℕ, dist ((T : X → X)^[j] y) ((T : X → X)^[j] (code a)) ≤ 2 * ε) :
    T y ∈ rectangle code (a.val 1) ∧
      ∀ j : ℕ, dist ((T : X → X)^[j] (T y)) ((T : X → X)^[j] (T (code a))) ≤ 2 * ε := by
  obtain ⟨b, symbol, coded⟩ := inside
  let same : b.val 0 = a.val 0 := symbol
  have product : ProductRelation T (2 * ε) (code a) (code b) (code (splice b a same)) :=
    fun j => ⟨splice_future T center code ε near b a same j,
      splice_past T center code ε near b a same j⟩
  have candidate : ProductRelation T (2 * ε) (code a) (code b) y := by
    intro j
    refine ⟨stable j, ?_⟩
    rw [coded, dist_self]
    linarith
  have identity : code (splice b a same) = y :=
    product_unique T c (2 * ε) expansive (by linarith) _ _ _ _ product candidate
  constructor
  · refine ⟨shift R (splice b a same), ?_, ?_⟩
    · change (shift R (splice b a same)).val 0 = a.val 1
      simpa only [shift_apply, zero_add] using splice_nonneg b a same 1 (by omega)
    · exact (intertwines _).trans (congrArg T identity)
  · intro j
    simpa only [Function.iterate_succ_apply] using stable (j + 1)

/-- The inverse image of the local unstable slice in the next rectangle
lies in the first literal cylinder-image rectangle. -/
theorem weak_unstable_transition (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
    (c ε : ℝ) (nonnegativeε : 0 ≤ ε)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (intertwines : ∀ a, code (shift R a) = T (code a))
    (a : Path R) (y : X) (inside : y ∈ rectangle code (a.val 1))
    (unstable : ∀ j : ℕ,
      dist ((T.symm : X → X)^[j] y) ((T.symm : X → X)^[j] (T (code a))) ≤ 2 * ε) :
    T.symm y ∈ rectangle code (a.val 0) ∧
      ∀ j : ℕ, dist ((T.symm : X → X)^[j] (T.symm y)) ((T.symm : X → X)^[j] (code a)) ≤ 2 * ε := by
  obtain ⟨b, symbol, coded⟩ := inside
  let next := shift R a
  have same : next.val 0 = b.val 0 := by
    simpa only [next, shift_apply, zero_add] using symbol.symm
  have product : ProductRelation T (2 * ε) (code b) (code next) (code (splice next b same)) :=
    fun j => ⟨splice_future T center code ε near next b same j,
      splice_past T center code ε near next b same j⟩
  have candidate : ProductRelation T (2 * ε) (code b) (code next) y := by
    intro j
    constructor
    · rw [coded, dist_self]
      linarith
    · simpa only [next, intertwines] using unstable j
  have identity : code (splice next b same) = y :=
    product_unique T c (2 * ε) expansive (by linarith) _ _ _ _ product candidate
  constructor
  · refine ⟨(shift R).symm (splice next b same), ?_, ?_⟩
    · change ((shift R).symm (splice next b same)).val 0 = a.val 0
      rw [shift_symm_apply]
      have previous := splice_nonpos next b same (-1) (by omega)
      simpa only [zero_sub, next, shift_apply, neg_add_cancel] using previous
    · exact (code_shift_inverse T code intertwines _).trans (congrArg T.symm identity)
  · intro j
    simpa only [Function.iterate_succ_apply, T.symm_apply_apply] using unstable (j + 1)

end LeanShared.BilateralShadowingCoding
