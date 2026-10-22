module
public import LeanShared.Analysis.NonstationarySymbolResolution
public import LeanShared.Analysis.NonlinearFourierPhaseGradient
import Mathlib.Tactic

/-! The actual smooth reciprocal-gradient symbols resolve the original
amplitude on its separated frequency support. No global separation is
required outside that support. -/
public noncomputable section
open scoped RealInnerProductSpace
namespace LeanShared.NonlinearSymbolPhaseResolution
variable {E ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem resolution (b:OrthonormalBasis ι ℝ E) {δ:ℝ} (positive:0<δ)
    {G:E→E} {w:E} (smooth:DifferentiableAt ℝ G w) (ξ η:E) (g χ:ℂ)
    (h:ι→ℂ)
    (formula:∀i,h i=χ*g*(SmoothNonstationarySymbol.coefficient positive (b i)
      (fderiv ℝ G w,(ξ,η)):ℂ))
    (gap:g≠0→χ≠0→δ≤‖SmoothNonstationarySymbol.gradient (fderiv ℝ G w,(ξ,η))‖^2):
    (∑i,(fderiv ℝ (NonlinearFourierPhaseGradient.phase G ξ η) w (b i):ℂ)*h i)=χ*g:=by
  by_cases hg:g=0
  · simp [formula,hg]
  by_cases hχ:χ=0
  · simp [formula,hχ]
  have raw:=NonstationarySymbolResolution.resolution b positive (fderiv ℝ G w,(ξ,η)) (gap hg hχ)
  have identity:(∑i,(fderiv ℝ (NonlinearFourierPhaseGradient.phase G ξ η) w (b i):ℂ)*h i)=
      (χ*g)*((∑i,inner ℝ (SmoothNonstationarySymbol.gradient (fderiv ℝ G w,(ξ,η))) (b i)*
        SmoothNonstationarySymbol.coefficient positive (b i) (fderiv ℝ G w,(ξ,η)):ℝ):ℂ):=by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [formula,NonlinearFourierPhaseGradient.derivative smooth]
    dsimp [SmoothNonstationarySymbol.gradient]
    ring
  rw [identity,raw,Complex.ofReal_one,mul_one]
end LeanShared.NonlinearSymbolPhaseResolution
