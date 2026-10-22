module
public import LeanShared.Analysis.FourierSchwartzLaplacian
public import LeanShared.Analysis.ConeFourierBlocks
import all Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Positivity

/-! A compact multiplier vanishing near zero has an actual Schwartz elliptic
parametrix of every finite order. No parametrix or derivative bound is assumed. -/
public noncomputable section
open Set Filter
open scoped SchwartzMap ContDiff Topology FourierTransform
namespace LeanShared.AnnularEllipticSymbol
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def divide (σ : 𝓢(E,ℂ)) (n : ℕ) (ξ : E) : ℂ :=
  σ ξ/(-((‖ξ‖:ℂ)^2))^n

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem denominator_nonzero (n : ℕ) {ξ : E} (nonzero : ξ ≠ 0) :
    (-((‖ξ‖:ℂ)^2))^n ≠ 0 :=
  pow_ne_zero n (neg_ne_zero.mpr (pow_ne_zero 2
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr nonzero))))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem smooth (σ : 𝓢(E,ℂ)) (ε : ℝ) (positive : 0 < ε)
    (collar : ∀ ξ, ‖ξ‖ < ε → σ ξ=0) (n : ℕ) : ContDiff ℝ ∞ (divide σ n) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases zero : ξ=0
  · subst ξ
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0:E) positive] with y hy
    change σ y/(-((‖y‖:ℂ)^2))^n=0
    rw [collar y (by simpa only [Metric.mem_ball,dist_zero_right] using hy),zero_div]
  · have normSmooth : ContDiffAt ℝ ∞ (fun y : E => (‖y‖:ℂ)) ξ :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp ξ (contDiffAt_norm ℝ zero)
    convert! (σ.smooth ⊤).contDiffAt.mul
      (((normSmooth.pow 2).neg.pow n).inv (denominator_nonzero n zero)) using 1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compact (σ : 𝓢(E,ℂ)) (support : HasCompactSupport σ) (n : ℕ) :
    HasCompactSupport (divide σ n) := by
  exact support.mul_right (f' := fun ξ => ((-((‖ξ‖:ℂ)^2))^n)⁻¹)

@[expose] def symbol (σ : 𝓢(E,ℂ)) (support : HasCompactSupport σ)
    (ε : ℝ) (positive : 0 < ε) (collar : ∀ ξ, ‖ξ‖ < ε → σ ξ=0) (n : ℕ) : 𝓢(E,ℂ) :=
  (compact σ support n).toSchwartzMap (smooth σ ε positive collar n)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem multiply (σ : 𝓢(E,ℂ)) (support : HasCompactSupport σ)
    (ε : ℝ) (positive : 0 < ε) (collar : ∀ ξ, ‖ξ‖ < ε → σ ξ=0) (n : ℕ) (ξ : E) :
    symbol σ support ε positive collar n ξ*((-((‖ξ‖:ℂ)^2))^n)=σ ξ := by
  by_cases zero : ξ=0
  · subst ξ
    have value := collar 0 (by simpa only [norm_zero] using positive)
    change (σ 0/(-((‖(0:E)‖:ℂ)^2))^n)*(-((‖(0:E)‖:ℂ)^2))^n=σ 0
    rw [value,zero_div,zero_mul]
  · exact div_mul_cancel₀ _ (denominator_nonzero n zero)
end LeanShared.AnnularEllipticSymbol
