module
public import LeanShared.Analysis.FourierBlockTestPairing
public import LeanShared.Analysis.AnnularEllipticReconstruction
import Mathlib.Tactic.Linarith

/-! An actual Schwartz dual cutoff, equal to one on the full dyadic annulus
and zero near the origin, constructed from the original radial cutoff. -/
public noncomputable section
open Set
open scoped SchwartzMap ContDiff
namespace LeanShared.AnnularDualCutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open ConeDyadicSymbols FourierSchwartzKernel
@[expose] def radialSymbol (χ : RadialCutoff) : 𝓢(E,ℂ) :=
  (low_hasCompactSupport χ).toSchwartzMap (low_smooth χ)
@[expose] def symbol (χ : RadialCutoff) : 𝓢(E,ℂ) :=
  (2:ℂ) • dilateSymbol (radialSymbol χ) 2 (by norm_num) -
  (2:ℂ) • dilateSymbol (radialSymbol χ) (1/4) (by norm_num)

omit [MeasurableSpace E] [BorelSpace E] in
theorem apply (χ : RadialCutoff) (ξ : E) :
    symbol χ ξ = (χ.toFun (‖ξ‖/2):ℂ) - (χ.toFun (4*‖ξ‖):ℂ) := by
  simp only [symbol,sub_apply,smul_apply,smul_eq_mul,dilateSymbol_apply]
  change 2*((χ.toFun ‖(2:ℝ)⁻¹ • ξ‖:ℂ)/2) -
    2*((χ.toFun ‖(1/4:ℝ)⁻¹ • ξ‖:ℂ)/2) = _
  norm_num [norm_smul,Real.norm_eq_abs,div_eq_mul_inv,mul_comm]
  ring


omit [MeasurableSpace E] [BorelSpace E] in
theorem one (χ : RadialCutoff) {ξ : E} (lower : 1/2 ≤ ‖ξ‖) (upper : ‖ξ‖ ≤ 2) :
    symbol χ ξ=1 := by
  rw [apply,χ.one (‖ξ‖/2) (by rw [abs_of_nonneg (by positivity)]; linarith),
    χ.zero (4*‖ξ‖) (by rw [abs_of_nonneg (by positivity)]; linarith)]
  norm_num

omit [MeasurableSpace E] [BorelSpace E] in
theorem collar (χ : RadialCutoff) {ξ : E} (small : ‖ξ‖ < 1/4) : symbol χ ξ=0 := by
  rw [apply,χ.one (‖ξ‖/2) (by rw [abs_of_nonneg (by positivity)]; linarith),
    χ.one (4*‖ξ‖) (by rw [abs_of_nonneg (by positivity)]; linarith)]
  norm_num

omit [MeasurableSpace E] [BorelSpace E] in
theorem compact (χ : RadialCutoff) : HasCompactSupport (symbol (E:=E) χ : E→ℂ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:E) 4)
  intro ξ outside
  have large : 4 < ‖ξ‖ := by
    simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using outside
  rw [apply,χ.zero (‖ξ‖/2) (by rw [abs_of_nonneg (by positivity)]; linarith),
    χ.zero (4*‖ξ‖) (by rw [abs_of_nonneg (by positivity)]; linarith)]
  norm_num
end LeanShared.AnnularDualCutoff
