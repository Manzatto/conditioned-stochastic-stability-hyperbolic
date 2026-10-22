module
public import LeanShared.Analysis.CompactCompletedDistributionFaithful
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Bochner integrals of realized core families in a compactly supported block completion are
the realizations of the pointwise integrals. The completed Schwartz pairings are faithful, and
Fubini identifies the pairings of both sides. -/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped SchwartzMap
namespace LeanShared.SchwartzAmbientBlocks
variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (D : Set E) (σ : ℕ × S → 𝓢(E, ℂ)) (t : S → ℝ)
  (bounded : SmoothCoreBounded μ hJ leaves D σ t)
  (pairBound : ∀ test, ∃ C : ℝ, ∀ f, ‖pairing D f test‖ ≤ C * ‖coreMap μ hJ leaves D σ t bounded f‖)

include pairBound in
theorem integral_coreLift (compact : IsCompact D) (a : E → ℂ) (acont : Continuous a)
    (ha : Integrable a) (f : E → SchwartzJetSpace.supportedCore D)
    (joint : Continuous (fun p : E × E => (f p.1).val p.2)) (B : ℝ)
    (hB : ∀ y x, ‖(f y).val x‖ ≤ B)
    (hint : Integrable (fun y => a y • DyadicCompletion.coreLift (coreMap μ hJ leaves D σ t bounded) (f y)))
    (F : SchwartzJetSpace.supportedCore D) (hF : ∀ x, F.val x = ∫ y, a y * (f y).val x) :
    ∫ y, a y • DyadicCompletion.coreLift (coreMap μ hJ leaves D σ t bounded) (f y) =
      DyadicCompletion.coreLift (coreMap μ hJ leaves D σ t bounded) F := by
  apply compact_completed_pairing_injective μ hJ leaves D σ t bounded pairBound compact
  apply LinearMap.ext
  intro φ
  let q := coreMap μ hJ leaves D σ t bounded
  let L := CompletedCorePairing.atTest q (pairing D) φ
  have each (y : E) : L (a y • DyadicCompletion.coreLift q (f y)) =
      ∫ x, a y * ((f y).val x * φ x) := by
    rw [map_smul, CompletedCorePairing.core q (pairing D) pairBound (f y) φ, smul_eq_mul]
    change a y * ∫ x, (f y).val x * φ x = _
    rw [← integral_const_mul]
  have product : Integrable (Function.uncurry fun (y x : E) => a y * ((f y).val x * φ x))
      (volume.prod volume) := by
    have base : Integrable (fun p : E × E => ‖a p.1‖ * (B * ‖φ p.2‖)) (volume.prod volume) :=
      ha.norm.mul_prod (φ.integrable.norm.const_mul B)
    refine base.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact ((acont.comp continuous_fst).mul (joint.mul (φ.continuous.comp continuous_snd))).aestronglyMeasurable
    · rw [Function.uncurry_apply_pair, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hB _ _) (norm_nonneg _))
        (norm_nonneg _)
  have fubini : (∫ y, ∫ x, a y * ((f y).val x * φ x)) = ∫ x, F.val x * φ x := by
    rw [integral_integral_swap product]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [hF, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only
    ring
  have final : L (∫ y, a y • DyadicCompletion.coreLift q (f y)) = L (DyadicCompletion.coreLift q F) :=
    calc L (∫ y, a y • DyadicCompletion.coreLift q (f y))
        = ∫ y, L (a y • DyadicCompletion.coreLift q (f y)) :=
          (ContinuousLinearMap.integral_comp_comm L hint).symm
      _ = ∫ y, ∫ x, a y * ((f y).val x * φ x) := integral_congr_ae (ae_of_all _ each)
      _ = ∫ x, F.val x * φ x := fubini
      _ = L (DyadicCompletion.coreLift q F) :=
          (CompletedCorePairing.core q (pairing D) pairBound F φ).symm
  exact final

section CutoffConvolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The supported core element `cut · (a ⋆ ρ)`. -/
@[expose] def cutoffConvolution (cut ρ : 𝓢(E, ℂ)) (cutCompact : HasCompactSupport (cut : E → ℂ))
    (ρc : HasCompactSupport (ρ : E → ℂ)) (a : E → ℂ) (acont : Continuous a) :
    SchwartzJetSpace.supportedCore (tsupport (cut : E → ℂ)) :=
  ⟨(cutCompact.mul_right (f' := fun x => ∫ t, a t * ρ (x - t))).toSchwartzMap
      ((cut.smooth ⊤).mul (ρc.contDiff_convolution_right (μ := volume)
        (ContinuousLinearMap.mul ℝ ℂ) acont.locallyIntegrable (ρ.smooth ⊤))),
    fun x hx => by
      change cut x * ∫ t, a t * ρ (x - t) = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]⟩

theorem cutoffConvolution_apply (cut ρ : 𝓢(E, ℂ)) (cutCompact : HasCompactSupport (cut : E → ℂ))
    (ρc : HasCompactSupport (ρ : E → ℂ)) (a : E → ℂ) (acont : Continuous a) (x : E) :
    (cutoffConvolution cut ρ cutCompact ρc a acont).val x = cut x * ∫ t, a t * ρ (x - t) := rfl

/-- Two successive convolutions through the translation parameter are one convolution with
`κ(y) = ∫ ρ(s) ρ'(y + s) ds`. -/
theorem double_convolution (G ρ ρ' : E → ℂ) (Gc : Continuous G) (Gcs : HasCompactSupport G)
    (ρc : Continuous ρ) (ρcs : HasCompactSupport ρ) (ρ'c : Continuous ρ')
    (ρ'cs : HasCompactSupport ρ') (x : E) :
    ∫ t, (∫ z, G z * ρ (z - t)) * ρ' (x - t) =
      ∫ y, (∫ s, ρ s * ρ' (y + s)) * G (x - y) := by
  obtain ⟨Bρ, hBρ⟩ := ρc.norm.bddAbove_range_of_hasCompactSupport ρcs.norm
  have hBρx : ∀ u, ‖ρ u‖ ≤ Bρ := fun u => hBρ ⟨u, rfl⟩
  have product : Integrable (Function.uncurry fun (t z : E) => G z * ρ (z - t) * ρ' (x - t))
      (volume.prod volume) := by
    have base : Integrable (fun p : E × E => ‖ρ' (x - p.1)‖ * (‖G p.2‖ * Bρ)) (volume.prod volume) :=
      ((ρ'c.integrable_of_hasCompactSupport ρ'cs).comp_sub_left x).norm.mul_prod
        ((Gc.integrable_of_hasCompactSupport Gcs).norm.mul_const Bρ)
    refine base.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact (((Gc.comp continuous_snd).mul (ρc.comp (continuous_snd.sub continuous_fst))).mul
        (ρ'c.comp (continuous_const.sub continuous_fst))).aestronglyMeasurable
    · rw [Function.uncurry_apply_pair, norm_mul, norm_mul]
      calc ‖G p.2‖ * ‖ρ (p.2 - p.1)‖ * ‖ρ' (x - p.1)‖ ≤ ‖G p.2‖ * Bρ * ‖ρ' (x - p.1)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hBρx _) (norm_nonneg _))
              (norm_nonneg _)
        _ = ‖ρ' (x - p.1)‖ * (‖G p.2‖ * Bρ) := by ring
  calc ∫ t, (∫ z, G z * ρ (z - t)) * ρ' (x - t)
      = ∫ t, ∫ z, G z * ρ (z - t) * ρ' (x - t) := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        dsimp only
        rw [← integral_mul_const]
    _ = ∫ z, ∫ t, G z * ρ (z - t) * ρ' (x - t) := integral_integral_swap product
    _ = ∫ z, (∫ s, ρ s * ρ' (x - z + s)) * G z := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        dsimp only
        rw [mul_comm, ← integral_const_mul]
        have shift := integral_sub_left_eq_self (μ := volume)
          (fun s => G z * (ρ s * ρ' (x - z + s))) z
        rw [← shift]
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only
        rw [show x - z + (z - t) = x - t by abel]
        ring
    _ = ∫ y, (∫ s, ρ s * ρ' (y + s)) * G (x - y) := by
        have shift := integral_sub_left_eq_self (μ := volume)
          (fun y => (∫ s, ρ s * ρ' (y + s)) * G (x - y)) x
        rw [← shift]
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only
        rw [sub_sub_cancel]

end CutoffConvolution

end LeanShared.SchwartzAmbientBlocks
