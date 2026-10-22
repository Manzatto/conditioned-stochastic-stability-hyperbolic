module

public import LeanShared.Analysis.GraphBlockJacobianProduct
public import LeanShared.Analysis.FiniteJetWords

/-! The chronological product is the derivative of the literal nonlinear
finite word, evaluated along its actual orbit. -/
public noncomputable section
namespace LeanShared.ChronologicalDerivativeProduct
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
open GraphBlockJacobianProduct FiniteJetComposition

theorem hasFDerivAt_word (f : ℕ → E → E) (z : E) (n : ℕ)
    (smooth : ∀ i < n, DifferentiableAt ℝ (f i) (word f i z)) :
    HasFDerivAt (word f n)
      (product (fun i => fderiv ℝ (f i) (word f i z)) n) z := by
  induction n with
  | zero => exact hasFDerivAt_id z
  | succ n ih =>
    have previous := ih (fun i hi => smooth i (hi.trans (Nat.lt_succ_self n)))
    exact (smooth n (Nat.lt_succ_self n)).hasFDerivAt.comp z previous

end LeanShared.ChronologicalDerivativeProduct
