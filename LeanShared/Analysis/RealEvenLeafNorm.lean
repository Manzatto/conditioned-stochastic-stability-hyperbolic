module

public import LeanShared.Analysis.RealEvenFourierBlocks
public import LeanShared.Analysis.SchwartzAmbientBlocks

/-! Actual ambient leaf L1 norms and dyadic supremum norms preserve complex
conjugation for real even symbols. No completed-space star bound is supplied. -/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped SchwartzMap ComplexConjugate ENNReal
namespace LeanShared.RealEvenFourierBlocks

variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)

omit [FiniteDimensional ℝ E] in
theorem realization_conjugate_norm (f : 𝓢(E, ℂ)) :
    ‖SchwartzAmbientRealization.realization μ hJ leaves (conjugate f)‖ =
      ‖SchwartzAmbientRealization.realization μ hJ leaves f‖ := by
  rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
  congr 1
  funext a
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [SchwartzAmbientRealization.realization_ae μ hJ leaves (conjugate f) a,
    SchwartzAmbientRealization.realization_ae μ hJ leaves f a] with x hx hy
  rw [hx, hy, conjugate_apply, Complex.norm_conj]

def supportedConjugate {D : Set E} (f : SchwartzJetSpace.supportedCore D) :
    SchwartzJetSpace.supportedCore D :=
  ⟨conjugate f.val, fun x hx => by rw [conjugate_apply, f.property x hx]; simp⟩

theorem weightedBlock_conjugate_norm (D : Set E) (σ : ℕ × S → 𝓢(E, ℂ)) (t : S → ℝ)
    (hreal : ∀ j ξ, conj (σ j ξ) = σ j ξ) (heven : ∀ j ξ, σ j (-ξ) = σ j ξ)
    (f : SchwartzJetSpace.supportedCore D) (j : ℕ × S) :
    ‖SchwartzAmbientBlocks.weightedBlock μ hJ leaves D σ t j (supportedConjugate f)‖ =
      ‖SchwartzAmbientBlocks.weightedBlock μ hJ leaves D σ t j f‖ := by
  change ‖SchwartzAmbientBlocks.weight t j •
      SchwartzAmbientRealization.realization μ hJ leaves
        (ConeFourierBlocks.block (σ j) (conjugate f.val))‖ =
    ‖SchwartzAmbientBlocks.weight t j •
      SchwartzAmbientRealization.realization μ hJ leaves (ConeFourierBlocks.block (σ j) f.val)‖
  rw [block_conjugate (σ j) f.val (hreal j) (heven j), norm_smul, norm_smul,
    realization_conjugate_norm]

theorem coreMap_conjugate_norm (D : Set E) (σ : ℕ × S → 𝓢(E, ℂ)) (t : S → ℝ)
    (bounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D σ t)
    (hreal : ∀ j ξ, conj (σ j ξ) = σ j ξ) (heven : ∀ j ξ, σ j (-ξ) = σ j ξ)
    (f : SchwartzJetSpace.supportedCore D) :
    ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D σ t bounded (supportedConjugate f)‖ =
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D σ t bounded f‖ := by
  rw [SchwartzAmbientBlocks.coreMap_norm, SchwartzAmbientBlocks.coreMap_norm]
  congr 1
  funext j
  exact weightedBlock_conjugate_norm μ hJ leaves D σ t hreal heven f j

end LeanShared.RealEvenFourierBlocks
