module

public import LeanShared.Analysis.NormCompletionEquivalence

/-!
# Bounded comparison of actual core completions

A cited comparison of two smooth-core norms constructs a canonical bounded
map of their actual completions. Agreement of continuous distribution
realizations extends from the common core by density, and proves injectivity
when the source realization separates points. Thus a cross-cone comparison
need not supply a completed embedding or any compactness conclusion.
-/

@[expose] public noncomputable section

namespace LeanShared.NormCompletionComparison

open DyadicCompletion

variable {Core B F : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (q : Core →ₗ[ℂ] B) (r : Core →ₗ[ℂ] F)
  (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ c, ‖r c‖ ≤ C * ‖q c‖)

def comparison : closedCore q →L[ℂ] closedCore r :=
  (coreLift r).extendOfNorm (coreLift q)

include hbound in
@[simp] theorem comparison_core (c : Core) :
    comparison q r (coreLift q c) = coreLift r c :=
  LinearMap.extendOfNorm_eq (f := coreLift r) (e := coreLift q)
    (coreLift_dense q) ⟨C, hbound⟩ c

include hC hbound in
theorem comparison_norm_le : ‖comparison q r‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (coreLift_dense q) hC hbound

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  (p : closedCore q →L[ℂ] D) (s : closedCore r →L[ℂ] D)
  (hcore : ∀ c, s (coreLift r c) = p (coreLift q c))

include hbound hcore in
theorem realization_comp_comparison : s.comp (comparison q r) = p := by
  apply ContinuousLinearMap.ext
  intro z
  refine (coreLift_dense q).induction_on
    (p := fun x => s (comparison q r x) = p x) z
    (isClosed_eq (s.continuous.comp (comparison q r).continuous) p.continuous) ?_
  intro c
  rw [comparison_core q r C hbound, hcore]

include hbound hcore in
theorem comparison_injective (hp : Function.Injective p) :
    Function.Injective (comparison q r) := by
  intro x y hxy
  apply hp
  have h := realization_comp_comparison q r C hbound p s hcore
  have hx := congrArg (fun T : closedCore q →L[ℂ] D => T x) h
  have hy := congrArg (fun T : closedCore q →L[ℂ] D => T y) h
  rw [← hx, ← hy]
  exact congrArg s hxy

include hbound in
theorem comparison_unique (T : closedCore q →L[ℂ] closedCore r)
    (hT : ∀ c, T (coreLift q c) = coreLift r c) : T = comparison q r := by
  apply ContinuousLinearMap.ext
  intro z
  refine (coreLift_dense q).induction_on
    (p := fun x => T x = comparison q r x) z
    (isClosed_eq T.continuous (comparison q r).continuous) ?_
  intro c
  rw [hT, comparison_core q r C hbound]

end LeanShared.NormCompletionComparison
