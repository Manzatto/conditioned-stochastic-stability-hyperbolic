module
public import LeanShared.Analysis.MollifierKernel
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! Real nonnegative Schwartz mollifiers supported in any ball, with a real nonnegative
correlation kernel of unit mass supported in the doubled ball. -/
public noncomputable section
open MeasureTheory Set
open scoped SchwartzMap ContDiff
namespace LeanShared.RealMollifierSupply

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem supply (ε : ℝ) (hε : 0 < ε) :
    ∃ (ρ : 𝓢(E, ℂ)) (κ : E → ℝ), HasCompactSupport (ρ : E → ℂ) ∧
      (∀ s, ε < ‖s‖ → ρ s = 0) ∧ ∫ s, ρ s = 1 ∧ ∫ s, ‖ρ s‖ ≤ 1 ∧
      (∀ t, MollifierKernel.kernel ρ ρ t = (κ t : ℂ)) ∧ Continuous κ ∧ (∀ t, 0 ≤ κ t) ∧
      HasCompactSupport κ ∧ (∀ t, 2 * ε < ‖t‖ → κ t = 0) ∧ ∫ t, κ t = 1 := by
  let f : ContDiffBump (0 : E) := ⟨ε / 2, ε, by positivity, by linarith⟩
  let ρR : E → ℝ := f.normed volume
  have compactC : HasCompactSupport (fun s => (ρR s : ℂ)) :=
    f.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  have smoothC : ContDiff ℝ ∞ (fun s => (ρR s : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp f.contDiff_normed
  let ρ : 𝓢(E, ℂ) := compactC.toSchwartzMap smoothC
  have ρapply : ∀ s, ρ s = (ρR s : ℂ) := fun _ => rfl
  have outside : ∀ s, ε < ‖s‖ → ρR s = 0 := fun s hs => Function.notMem_support.mp fun h => by
    rw [f.support_normed_eq, Metric.mem_ball, dist_zero_right] at h
    exact absurd hs (not_lt.mpr h.le)
  have massR : ∫ s, ρR s = 1 := f.integral_normed
  have mass : ∫ s, ρ s = 1 := by
    simp only [ρapply]
    rw [integral_complex_ofReal, massR, Complex.ofReal_one]
  have nonneg : ∀ s, 0 ≤ ρR s := f.nonneg_normed
  let κ : E → ℝ := fun t => ∫ s, ρR s * ρR (t + s)
  have kernelEq : ∀ t, MollifierKernel.kernel ρ ρ t = (κ t : ℂ) := fun t => by
    unfold MollifierKernel.kernel
    simp only [ρapply, κ, ← Complex.ofReal_mul]
    exact integral_complex_ofReal
  have ρc : Continuous (ρ : E → ℂ) := ρ.continuous
  have ρcs : HasCompactSupport (ρ : E → ℂ) := compactC
  have kernelCont := MollifierKernel.continuous ρ ρ ρc ρcs ρc ρcs
  have κcont : Continuous κ := by
    have : κ = fun t => (MollifierKernel.kernel ρ ρ t).re := funext fun t => by
      rw [kernelEq, Complex.ofReal_re]
    rw [this]
    exact Complex.continuous_re.comp kernelCont
  have ρout : ∀ s, ε < ‖s‖ → ρ s = 0 := fun s hs => by rw [ρapply, outside s hs, Complex.ofReal_zero]
  have κout : ∀ t, 2 * ε < ‖t‖ → κ t = 0 := fun t ht => by
    have := MollifierKernel.zero_outside ρ ρ ρout ρout t (by linarith)
    rw [kernelEq] at this
    exact_mod_cast this
  refine ⟨ρ, κ, ρcs, ρout, mass, ?_, kernelEq, κcont, fun t => integral_nonneg fun s =>
    mul_nonneg (nonneg s) (nonneg _), ?_, κout, ?_⟩
  · simp only [ρapply, Complex.norm_real, Real.norm_of_nonneg (nonneg _)]
    exact massR.le
  · exact HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * ε)) fun t ht =>
      κout t (by rwa [Metric.mem_closedBall, dist_zero_right, not_le] at ht)
  · have total := MollifierKernel.integral ρ ρ ρc ρcs ρc ρcs
    simp only [kernelEq, mass, mul_one] at total
    rw [integral_complex_ofReal] at total
    exact_mod_cast total

end LeanShared.RealMollifierSupply
