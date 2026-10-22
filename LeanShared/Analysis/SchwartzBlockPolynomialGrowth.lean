module
public import LeanShared.Analysis.SchwartzAmbientBlocks
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! The actual weighted supremum norm supplies polynomial growth bounds
for every unweighted physical Fourier block. -/
public noncomputable section
open MeasureTheory Set
open scoped SchwartzMap
namespace LeanShared.SchwartzAmbientBlocks
variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (D : Set E) (σ : ℕ×S → 𝓢(E,ℂ)) (t : S→ℝ)
  (bounded : SmoothCoreBounded μ hJ leaves D σ t)

theorem unweighted_bound (q : ℕ) (margin : ∀ s, -t s ≤ q)
    (f : SchwartzJetSpace.supportedCore D) (j : ℕ×S) :
    ‖block μ hJ leaves D σ j f‖ ≤
      ‖coreMap μ hJ leaves D σ t bounded f‖*((2:ℝ)^j.1)^q := by
  let w : ℝ := (2:ℝ)^(t j.2*j.1)
  have positive : 0<w := Real.rpow_pos_of_pos (by norm_num) _
  have actual := lp.norm_apply_le_norm ENNReal.top_ne_zero
    (coreMap μ hJ leaves D σ t bounded f) j
  change ‖weight t j • block μ hJ leaves D σ j f‖ ≤ _ at actual
  rw [norm_smul] at actual
  have weightNorm : ‖weight t j‖=w := by
    simp only [weight,Complex.norm_real,Real.norm_eq_abs]
    change |w|=w
    exact abs_of_pos positive
  rw [weightNorm] at actual
  have inverse : w⁻¹ ≤ ((2:ℝ)^j.1)^q := by
    change ((2:ℝ)^(t j.2*j.1))⁻¹ ≤ _
    rw [← Real.rpow_neg (by norm_num)]
    have power : ((2:ℝ)^j.1)^q=(2:ℝ)^((q:ℝ)*j.1) := by
      rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [power]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right (margin j.2) (Nat.cast_nonneg j.1 : (0:ℝ)≤j.1)]
  calc
    _ = w⁻¹*(w*‖block μ hJ leaves D σ j f‖) := by
      rw [← mul_assoc,inv_mul_cancel₀ (ne_of_gt positive),one_mul]
    _ ≤ w⁻¹*‖coreMap μ hJ leaves D σ t bounded f‖ :=
      mul_le_mul_of_nonneg_left actual (inv_nonneg.mpr positive.le)
    _ ≤ ((2:ℝ)^j.1)^q*‖coreMap μ hJ leaves D σ t bounded f‖ :=
      mul_le_mul_of_nonneg_right inverse (norm_nonneg _)
    _ = _ := mul_comm _ _
end LeanShared.SchwartzAmbientBlocks
