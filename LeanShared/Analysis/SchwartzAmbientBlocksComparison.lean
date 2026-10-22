module
public import LeanShared.Analysis.SchwartzAmbientBlocks

/-! The physical block norm depends only on the ambient leaf measures: two
leaf families whose index sets correspond bijectively with equal ambient
measures give blocks of equal norm at every dyadic index. -/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set
namespace LeanShared.SchwartzAmbientBlocksComparison
open SchwartzJetSpace SchwartzAmbientBlocks
variable {E U₁ U₂ A₁ A₂ S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U₁] [NormedSpace ℝ U₁] [FiniteDimensional ℝ U₁]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [NormedAddCommGroup U₂] [NormedSpace ℝ U₂] [FiniteDimensional ℝ U₂]
  [MeasurableSpace U₂] [BorelSpace U₂]
  (μ₁ : Measure U₁) [μ₁.IsAddHaarMeasure] (μ₂ : Measure U₂) [μ₂.IsAddHaarMeasure]
  {J₁ J₂ : ℝ} (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂)
  (leaves₁ : A₁ → GraphLeafNorm.GraphLeaf U₁ E J₁)
  (leaves₂ : A₂ → GraphLeafNorm.GraphLeaf U₂ E J₂)

theorem realization_entry_norm (g : SchwartzMap E ℂ) (a₁ : A₁) (a₂ : A₂)
    (same : (leaves₁ a₁).measure μ₁ = (leaves₂ a₂).measure μ₂) :
    ‖SchwartzAmbientRealization.linearMap μ₁ hJ₁ leaves₁ g a₁‖ =
      ‖SchwartzAmbientRealization.linearMap μ₂ hJ₂ leaves₂ g a₂‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (SchwartzAmbientRealization.linearMap_ae μ₁ hJ₁ leaves₁ g a₁),
    eLpNorm_congr_ae (SchwartzAmbientRealization.linearMap_ae μ₂ hJ₂ leaves₂ g a₂), same]

variable (e : A₁ ≃ A₂) (same : ∀ a, (leaves₁ a).measure μ₁ = (leaves₂ (e a)).measure μ₂)

include same in
theorem realization_norm (g : SchwartzMap E ℂ) :
    ‖SchwartzAmbientRealization.linearMap μ₁ hJ₁ leaves₁ g‖ =
      ‖SchwartzAmbientRealization.linearMap μ₂ hJ₂ leaves₂ g‖ := by
  apply le_antisymm
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun a => ?_
    rw [realization_entry_norm μ₁ μ₂ hJ₁ hJ₂ leaves₁ leaves₂ g a (e a) (same a)]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ _
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun a => ?_
    have back : (leaves₁ (e.symm a)).measure μ₁ = (leaves₂ a).measure μ₂ := by
      have := same (e.symm a)
      rwa [e.apply_symm_apply] at this
    rw [← realization_entry_norm μ₁ μ₂ hJ₁ hJ₂ leaves₁ leaves₂ g (e.symm a) a back]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ _

variable (D : Set E) (σ : ℕ × S → SchwartzMap E ℂ) (t : S → ℝ)
  (bounded₁ : SmoothCoreBounded μ₁ hJ₁ leaves₁ D σ t)
  (bounded₂ : SmoothCoreBounded μ₂ hJ₂ leaves₂ D σ t)

include same in
/-- Physical block cores built from leaf families with corresponding equal
ambient measures have equal block norms at every dyadic index. -/
theorem coreMap_entry_norm (f : supportedCore D) (j : ℕ × S) :
    ‖coreMap μ₁ hJ₁ leaves₁ D σ t bounded₁ f j‖ = ‖coreMap μ₂ hJ₂ leaves₂ D σ t bounded₂ f j‖ := by
  change ‖weight t j • SchwartzAmbientRealization.linearMap μ₁ hJ₁ leaves₁
      (ConeFourierBlocks.block (σ j) f.val)‖ =
    ‖weight t j • SchwartzAmbientRealization.linearMap μ₂ hJ₂ leaves₂
      (ConeFourierBlocks.block (σ j) f.val)‖
  rw [norm_smul, norm_smul,
    realization_norm μ₁ μ₂ hJ₁ hJ₂ leaves₁ leaves₂ e same]

end LeanShared.SchwartzAmbientBlocksComparison
