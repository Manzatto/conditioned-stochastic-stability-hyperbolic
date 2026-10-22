module

public import LeanShared.Dynamics.FiniteSymbolicBranchLifts
public import LeanShared.Dynamics.RectangleFourWayRefinement

/-! The first two classifier steps in the actual Markov refinement:
base memberships propagate along a stable atom slice, and stable-hit
classifiers agree along the resulting stable slice in a target rectangle.
The unstable-hit transport is the separate bracket-covariance step.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit ExpansiveLocalProduct
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

/-- Membership of the image in a cylinder has an actual incoming coded branch. -/
theorem exists_branch_to (T : X ≃ₜ X) (code : Path R → X)
    (intertwines : ∀ a, code (shift R a) = T (code a))
    (x : X) (i : A) (inside : T x ∈ rectangle code i) :
    ∃ a : Path R, code a = x ∧ a.val 1 = i := by
  obtain ⟨b, symbol, coded⟩ := inside
  refine ⟨(shift R).symm b, ?_, ?_⟩
  · exact (code_shift_inverse T code intertwines b).trans (by rw [coded, T.symm_apply_apply])
  · rw [shift_symm_apply, sub_self]
    exact symbol

variable (T : X ≃ₜ X) (center : A → X) (code : Path R → X) (c ε : ℝ)
    (nonnegativeε : 0 ≤ ε)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (intertwines : ∀ a, code (shift R a) = T (code a))
include nonnegativeε expansive small near intertwines

theorem stable_base_membership_forward_imp (x y : X)
    (sameBase : ∀ i : A, x ∈ rectangle code i ↔ y ∈ rectangle code i)
    (stable : ∀ j : ℕ, dist ((T : X → X)^[j] y) ((T : X → X)^[j] x) ≤ 2 * ε)
    (i : A) (inside : T x ∈ rectangle code i) : T y ∈ rectangle code i := by
  obtain ⟨a, coded, next⟩ := exists_branch_to T code intertwines x i inside
  have source : x ∈ rectangle code (a.val 0) := ⟨a, rfl, coded⟩
  have sourceY : y ∈ rectangle code (a.val 0) := (sameBase _).mp source
  have stableA : ∀ j : ℕ, dist ((T : X → X)^[j] y) ((T : X → X)^[j] (code a)) ≤ 2 * ε := by
    simpa only [coded] using stable
  have result := (weak_stable_transition T center code c ε nonnegativeε expansive small near intertwines
    a y sourceY stableA).1
  simpa only [next] using result

/-- Equal base classifiers remain equal under the dynamics on a stable atom slice. -/
theorem stable_base_membership_forward (x y : X)
    (sameBase : ∀ i : A, x ∈ rectangle code i ↔ y ∈ rectangle code i)
    (stable : ∀ j : ℕ, dist ((T : X → X)^[j] y) ((T : X → X)^[j] x) ≤ 2 * ε) (i : A) :
    T x ∈ rectangle code i ↔ T y ∈ rectangle code i := by
  constructor
  · exact stable_base_membership_forward_imp T center code c ε nonnegativeε expansive small near intertwines
      x y sameBase stable i
  · apply stable_base_membership_forward_imp T center code c ε nonnegativeε expansive small near intertwines
      y x (fun a => (sameBase a).symm) _ i
    intro j
    rw [dist_comm]
    exact stable j

end LeanShared.BilateralShadowingCoding

namespace LeanShared.ExpansiveLocalProduct
open Set RectangleFourWayRefinement
variable {X : Type*} [MetricSpace X]

/-- A forward-close pair in a rectangle has identical stable-hit classifiers. -/
theorem stableHit_iff_of_forward_close (T : X ≃ₜ X) (c δ : ℝ) (nonnegativeδ : 0 ≤ δ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c) (S : Set X) (bracket : S × S → S)
    (bounds : ∀ p, ProductRelation T δ p.1.val p.2.val (bracket p).val)
    (idempotent : ∀ x, bracket (x, x) = x)
    (band : ∀ x y u v, bracket (bracket (x, y), bracket (u, v)) = bracket (x, v))
    (U : Set S) (x y : S)
    (stable : ∀ j : ℕ, dist ((T : X → X)^[j] y.val) ((T : X → X)^[j] x.val) ≤ δ) :
    StableHit bracket U x ↔ StableHit bracket U y := by
  have equal := (stable_iff_bracket T c δ nonnegativeδ expansive small S bracket bounds x y).mp stable
  have identity := stableHit_bracket bracket idempotent band U x y
  rw [equal] at identity
  exact identity.symm

end LeanShared.ExpansiveLocalProduct
