module
public import LeanShared.Analysis.SchwartzCompletedDistributionFaithful
public import LeanShared.Analysis.CompactSmoothCutoff

/-! Compact support constructs the cutoff needed for faithful completed
distribution realization. No additional cutoff or separation input remains. -/
public noncomputable section
open MeasureTheory Set
open scoped SchwartzMap
namespace LeanShared.SchwartzAmbientBlocks
variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A→GraphLeafNorm.GraphLeaf U E J)
  (D : Set E) (σ : ℕ×S→𝓢(E,ℂ)) (t : S→ℝ)
  (bounded : SmoothCoreBounded μ hJ leaves D σ t)
  (pairBound : ∀ test,∃ C:ℝ,∀ f,‖pairing D f test‖≤C*‖coreMap μ hJ leaves D σ t bounded f‖)


theorem compact_completed_pairing_injective (compact : IsCompact D) : Function.Injective
    (CompletedCorePairing.pairing (coreMap μ hJ leaves D σ t bounded) (pairing D) pairBound) := by
  obtain ⟨ψ,smooth,supported,_,_,one⟩ := CompactSmoothCutoff.exists_cutoff
    compact isOpen_univ (subset_univ D)
  let χ : 𝓢(E,ℂ) := (supported.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp smooth)
  apply completed_pairing_injective μ hJ leaves D σ t bounded pairBound χ
  intro y hy
  change (ψ y : ℂ)=1
  rw [one hy]
  rfl
end LeanShared.SchwartzAmbientBlocks
