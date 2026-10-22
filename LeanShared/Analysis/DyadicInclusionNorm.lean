module

public import LeanShared.Analysis.DyadicCompletion

/-! # The actual dyadic weakening is a contraction -/

@[expose] public noncomputable section
namespace LeanShared.DyadicInclusionNorm
open DyadicCompletion
variable {Core F S : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (q : Core →ₗ[ℂ] BlockSpace (F := F) (S := S)) (η : ℝ) (hη : 0 < η)
  (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s)

theorem norm_exactInclusion_le (z : closedCore q) :
    ‖exactInclusion q η hη δ hδ z‖ ≤ ‖z‖ := by
  change ‖(exactInclusion q η hη δ hδ z : BlockSpace (F := F) (S := S))‖ ≤ ‖z‖
  apply lp.norm_le_of_forall_le (norm_nonneg z)
  intro j
  rw [exactInclusion_apply, norm_smul]
  have hw := branchWeight_norm_le (fun s => η + δ s) (fun s => add_nonneg hη.le (hδ s)) j
  change ‖(((2 : ℝ) ^ (-(η + δ j.2) * j.1) : ℝ) : ℂ)‖ ≤ 1 at hw
  exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans
    (by
      rw [one_mul]
      change ‖(z : BlockSpace (F := F) (S := S)) j‖ ≤ ‖(z : BlockSpace (F := F) (S := S))‖
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z : BlockSpace (F := F) (S := S)) j)

end LeanShared.DyadicInclusionNorm
