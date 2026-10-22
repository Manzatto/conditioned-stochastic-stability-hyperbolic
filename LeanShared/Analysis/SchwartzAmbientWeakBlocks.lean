module
public import LeanShared.Analysis.SchwartzAmbientBlocks

/-! The exact dyadic weakening of the physical block core is the physical
block core with the lowered exponents: the weights multiply. Hence the
weak norm of a smooth input equals its block norm at the lowered exponents. -/
public noncomputable section
open MeasureTheory Set
namespace LeanShared.SchwartzAmbientWeakBlocks
open SchwartzJetSpace SchwartzAmbientBlocks
variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (D : Set E) (σ : ℕ × S → SchwartzMap E ℂ) (t : S → ℝ)

theorem weak_coreMap_norm (hbounded : SmoothCoreBounded μ hJ leaves D σ t)
    (η : ℝ) (hη : 0 < η) (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s)
    (hweak : SmoothCoreBounded μ hJ leaves D σ (fun s => t s - (η + δ s)))
    (f : supportedCore D) :
    ‖DyadicCompletion.exactInclusion (coreMap μ hJ leaves D σ t hbounded) η hη δ hδ
      (DyadicCompletion.coreLift (coreMap μ hJ leaves D σ t hbounded) f)‖ =
    ‖coreMap μ hJ leaves D σ (fun s => t s - (η + δ s)) hweak f‖ := by
  rw [← Submodule.norm_coe]
  congr 1
  apply lp.ext
  funext j
  rw [DyadicCompletion.exactInclusion_apply, DyadicCompletion.coe_coreLift]
  change (((2 : ℝ) ^ (-(η + δ j.2) * j.1) : ℝ) : ℂ) • (weight t j • block μ hJ leaves D σ j f) =
    weight (fun s => t s - (η + δ s)) j • block μ hJ leaves D σ j f
  rw [smul_smul]
  congr 1
  unfold weight
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by norm_num)]
  congr 2
  ring

end LeanShared.SchwartzAmbientWeakBlocks
