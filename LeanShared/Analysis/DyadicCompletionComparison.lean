module
public import LeanShared.Analysis.DyadicCompletion
public import LeanShared.Analysis.NormCompletionEquivalence

/-! Two dyadic block cores whose blocks have equal norms entry by entry have
isometric completions, also after any exact weakening; consequently
compactness of one exact weakening transfers to the other. -/
public noncomputable section
namespace LeanShared.DyadicCompletionComparison
open DyadicCompletion
variable {Core F₁ F₂ S : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]

omit [NormedSpace ℂ F₁] [NormedSpace ℂ F₂] in
theorem norm_eq_of_entries (x : BlockSpace (F := F₁) (S := S)) (y : BlockSpace (F := F₂) (S := S))
    (h : ∀ j, ‖x j‖ = ‖y j‖) : ‖x‖ = ‖y‖ :=
  le_antisymm
    (lp.norm_le_of_forall_le (norm_nonneg _) fun j =>
      (h j).le.trans (lp.norm_apply_le_norm ENNReal.top_ne_zero y j))
    (lp.norm_le_of_forall_le (norm_nonneg _) fun j =>
      (h j).ge.trans (lp.norm_apply_le_norm ENNReal.top_ne_zero x j))

variable (η : ℝ) (hη : 0 < η) (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s)

theorem exactInclusion_core (q : Core →ₗ[ℂ] BlockSpace (F := F₁) (S := S)) (c : Core) :
    exactInclusion q η hη δ hδ (coreLift q c) = coreLift (finalCore q η hη δ hδ) c := by
  change furtherInclusion q η hη δ hδ (inclusion q η hη (coreLift q c)) = _
  rw [show inclusion q η hη (coreLift q c) = coreLift (weakCore q η hη) c from
    lift_core _ _ _ _ c]
  exact lift_core _ _ _ _ c

variable (q₁ : Core →ₗ[ℂ] BlockSpace (F := F₁) (S := S))
  (q₂ : Core →ₗ[ℂ] BlockSpace (F := F₂) (S := S)) (h : ∀ c j, ‖q₁ c j‖ = ‖q₂ c j‖)

include h in
theorem finalCore_entry_norm (c : Core) (j : ℕ × S) :
    ‖finalCore q₁ η hη δ hδ c j‖ = ‖finalCore q₂ η hη δ hδ c j‖ := by
  change ‖branchWeight δ j • (((DyadicCompactness.dyadicFactor η ^ j.1 : ℝ) : ℂ) • q₁ c j)‖ =
    ‖branchWeight δ j • (((DyadicCompactness.dyadicFactor η ^ j.1 : ℝ) : ℂ) • q₂ c j)‖
  rw [norm_smul, norm_smul, norm_smul, norm_smul, h c j]

variable [CompleteSpace F₁] [CompleteSpace F₂]

include h in
/-- Compactness of an exact weakening transfers along entrywise norm equality. -/
theorem exactInclusion_isCompact_of_entries
    (compact : IsCompactOperator (exactInclusion q₂ η hη δ hδ)) :
    IsCompactOperator (exactInclusion q₁ η hη δ hδ) := by
  have hS : ∀ c, ‖q₁ c‖ = ‖q₂ c‖ := fun c => norm_eq_of_entries _ _ (h c)
  have hT : ∀ c, ‖finalCore q₁ η hη δ hδ c‖ = ‖finalCore q₂ η hη δ hδ c‖ := fun c =>
    norm_eq_of_entries _ _ (finalCore_entry_norm η hη δ hδ q₁ q₂ h c)
  let ES := NormCompletionEquivalence.equivalence q₁ q₂ hS
  let ET := NormCompletionEquivalence.equivalence (finalCore q₁ η hη δ hδ)
    (finalCore q₂ η hη δ hδ) hT
  have same : exactInclusion q₁ η hη δ hδ =
      ET.symm.toLinearIsometry.toContinuousLinearMap.comp
        ((exactInclusion q₂ η hη δ hδ).comp ES.toLinearIsometry.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro z
    refine (coreLift_dense q₁).induction_on
      (p := fun v => exactInclusion q₁ η hη δ hδ v =
        ET.symm.toLinearIsometry.toContinuousLinearMap.comp
          ((exactInclusion q₂ η hη δ hδ).comp ES.toLinearIsometry.toContinuousLinearMap) v) z
      (isClosed_eq (exactInclusion q₁ η hη δ hδ).continuous (ContinuousLinearMap.continuous _)) ?_
    intro c
    change exactInclusion q₁ η hη δ hδ (coreLift q₁ c) =
      ET.symm (exactInclusion q₂ η hη δ hδ (ES (coreLift q₁ c)))
    rw [NormCompletionEquivalence.equivalence_core, exactInclusion_core, exactInclusion_core,
      NormCompletionEquivalence.equivalence_symm_core]
  rw [same]
  exact (compact.comp_clm _).clm_comp _

end LeanShared.DyadicCompletionComparison
