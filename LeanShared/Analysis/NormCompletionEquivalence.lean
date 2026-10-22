module

public import LeanShared.Analysis.DyadicCompletion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Identifying completed core norms from exact norm equality

Two linear realizations of the same algebraic core with equal norms have the
same kernel. Mathlib's quotient descent makes the induced map on their ranges
well-defined, and its dense extension identifies the closures of those ranges
by a canonical complex linear isometry equivalence. The core maps need not be
injective; no isometry or surjectivity of the completed spaces is supplied.
-/

@[expose] public noncomputable section

namespace LeanShared.NormCompletionEquivalence

open DyadicCompletion

variable {Core B F : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (q : Core →ₗ[ℂ] B) (r : Core →ₗ[ℂ] F)
  (hnorm : ∀ c, ‖q c‖ = ‖r c‖)

include hnorm

/-- Exact equality of core norms discharges the quotient well-definedness. -/
theorem ker_eq : q.ker = r.ker := by
  ext c
  change q c = 0 ↔ r c = 0
  constructor
  · intro hc
    apply norm_eq_zero.mp
    rw [← hnorm c, hc, norm_zero]
  · intro hc
    apply norm_eq_zero.mp
    rw [hnorm c, hc, norm_zero]

/-- The induced bounded linear map on the first range is constructed by
descent through its kernel, rather than by assuming injectivity of the core. -/
def rangeMap : q.range →L[ℂ] F := r.compLeftInverse q

@[simp]
theorem rangeMap_core (c : Core) : rangeMap q r ⟨q c, ⟨c, rfl⟩⟩ = r c := by
  exact LinearMap.compLeftInverse_apply_of_bdd r q
    ⟨1, fun c => by simp [← hnorm c]⟩ c (q c) rfl

theorem rangeMap_norm (x : q.range) : ‖rangeMap q r x‖ = ‖x‖ := by
  obtain ⟨y, c, hc⟩ := x
  subst y
  rw [rangeMap_core q r hnorm]
  exact (hnorm c).symm

variable [CompleteSpace B] [CompleteSpace F]

/-- The canonical isometric identification of the two actual completions.
The extension constructs both inverses from dense range, with the range maps
descending through the equal kernels. -/
def equivalence : closedCore q ≃ₗᵢ[ℂ] closedCore r :=
  (LinearEquiv.refl ℂ Core).extendOfIsometry (coreLift q) (coreLift r)
    (coreLift_dense q) (coreLift_dense r) (fun c => (hnorm c).symm)

@[simp]
theorem equivalence_core (c : Core) :
    equivalence q r hnorm (coreLift q c) = coreLift r c := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ c

@[simp]
theorem equivalence_symm_core (c : Core) :
    (equivalence q r hnorm).symm (coreLift r c) = coreLift q c := by
  apply (equivalence q r hnorm).injective
  rw [LinearIsometryEquiv.apply_symm_apply, equivalence_core]

/-- Agreement on the common core determines the entire completed isometry. -/
theorem equivalence_unique (S : closedCore q ≃ₗᵢ[ℂ] closedCore r)
    (hS : ∀ c, S (coreLift q c) = coreLift r c) : S = equivalence q r hnorm := by
  apply DFunLike.ext
  intro z
  refine (coreLift_dense q).induction_on
    (p := fun x => S x = equivalence q r hnorm x) z
    (isClosed_eq S.continuous (equivalence q r hnorm).continuous) ?_
  intro c
  rw [hS, equivalence_core]

end LeanShared.NormCompletionEquivalence
