module

public import LeanShared.Dynamics.FiniteSymbolicBracketCovariance
import Mathlib.Tactic.Linarith

/-! Strong weak-transition lifts retain both adjacent symbols of the
original coded branch.  This provenance is needed for the unstable-hit
step in the Bowen--Sinai refinement, beyond mere rectangle membership.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit ExpansiveLocalProduct
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

omit [TopologicalSpace A] in
theorem stable_branch_lift (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
    (c ε : ℝ) (nonnegativeε : 0 ≤ ε)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (a : Path R) (y : X) (inside : y ∈ rectangle code (a.val 0))
    (stable : ∀ j : ℕ, dist ((T : X → X)^[j] y) ((T : X → X)^[j] (code a)) ≤ 2 * ε) :
    ∃ b : Path R, code b = y ∧ b.val 0 = a.val 0 ∧ b.val 1 = a.val 1 := by
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
  refine ⟨splice b a same,
    product_unique T c (2 * ε) expansive (by linarith) _ _ _ _ product candidate, ?_, ?_⟩
  · exact (splice_nonpos b a same 0 le_rfl).trans same
  · exact splice_nonneg b a same 1 (by omega)

theorem unstable_branch_lift (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
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
    ∃ b : Path R, code b = T.symm y ∧ b.val 0 = a.val 0 ∧ b.val 1 = a.val 1 := by
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
  refine ⟨(shift R).symm (splice next b same),
    (code_shift_inverse T code intertwines _).trans (congrArg T.symm identity), ?_, ?_⟩
  · rw [shift_symm_apply]
    have previous := splice_nonpos next b same (-1) (by omega)
    simpa only [zero_sub, next, shift_apply, neg_add_cancel] using previous
  · rw [shift_symm_apply, sub_self, splice_nonpos next b same 0 le_rfl]
    exact shift_apply R a 0

end LeanShared.BilateralShadowingCoding
