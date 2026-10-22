module
public import LeanShared.Analysis.CompletedCorePairingPhysicalBlocks
public import LeanShared.Analysis.SchwartzAmbientBlocks

/-! The distribution pairing on the actual completed physical block norm is
faithful. Every leafwise block is recovered by testing against cutoff kernels. -/
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
  (χ : 𝓢(E,ℂ)) (cutoff : ∀ y∈D,χ y=1)

@[expose] def completedBlock (j : ℕ×S) (a : A) :
    DyadicCompletion.closedCore (coreMap μ hJ leaves D σ t bounded)→L[ℂ]
      Lp ℂ 1 ((leaves a).measure μ) :=
  (lp.evalCLM ℂ _ (⊤ : ENNReal) a).comp
    ((DyadicCompletion.coordinate j).comp
      (DyadicCompletion.closedCore (coreMap μ hJ leaves D σ t bounded)).subtypeL)

include cutoff in
theorem completedBlock_pairing (z : DyadicCompletion.closedCore (coreMap μ hJ leaves D σ t bounded))
    (j : ℕ×S) (a : A) :
    completedBlock μ hJ leaves D σ t bounded j a z=ᵐ[(leaves a).measure μ]
      (fun x=>weight t j*CompletedCorePairing.pairing
        (coreMap μ hJ leaves D σ t bounded) (pairing D) pairBound z
        (SchwartzJetKernel.cutoffKernel χ (FourierSchwartzKernel.kernel (σ j)) x)) := by
  apply CompletedCorePairing.physical_block _ _ pairBound _
    (completedBlock μ hJ leaves D σ t bounded j a) _ _ ?_ z
  intro f
  exact coreMap_cutoffPairing_ae μ hJ leaves D σ t bounded χ cutoff f j a

include cutoff in
theorem completed_pairing_injective : Function.Injective
    (CompletedCorePairing.pairing (coreMap μ hJ leaves D σ t bounded) (pairing D) pairBound) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  have zeroPair : CompletedCorePairing.pairing
      (coreMap μ hJ leaves D σ t bounded) (pairing D) pairBound z=0 := hz
  apply Subtype.ext
  apply lp.ext
  funext j
  apply lp.ext
  funext a
  apply Lp.ext
  have actual := completedBlock_pairing μ hJ leaves D σ t bounded pairBound χ cutoff z j a
  filter_upwards [actual,Lp.coeFn_zero ℂ 1 ((leaves a).measure μ)] with x hx hzero
  have hx0 : completedBlock μ hJ leaves D σ t bounded j a z x=0 := by
    simpa only [zeroPair,LinearMap.zero_apply,mul_zero] using hx
  exact hx0.trans (by simpa using hzero.symm)
end LeanShared.SchwartzAmbientBlocks
