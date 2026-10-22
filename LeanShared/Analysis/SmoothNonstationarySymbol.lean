module
public import LeanShared.Analysis.SmoothSeparatedReciprocal
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-! A genuinely smooth nonstationary coefficient symbol in the matrix
and both frequencies. It is exactly the reciprocal-gradient coefficient
where the actual gradient separation holds. -/
public noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace LeanShared.SmoothNonstationarySymbol
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

@[expose] def gradient (p:(E→L[ℝ]E) × (E × E)):E:=p.1.adjoint p.2.2-p.2.1

@[expose] def coefficient {δ:ℝ} (positive:0<δ) (v:E)
    (p:(E→L[ℝ]E) × (E × E)):ℝ:=
  ⟪gradient p,v⟫*SmoothSeparatedReciprocal.function positive ⟪gradient p,gradient p⟫

theorem smooth_gradient:ContDiff ℝ ∞ (gradient (E:=E)):=by
  have adj:ContDiff ℝ ∞ (fun p:(E→L[ℝ]E) × (E × E)=>p.1.adjoint):=by
    convert! (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=E) (F:=E)).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
      (contDiff_fst (𝕜:=ℝ) (n:=∞) (E:=E→L[ℝ]E) (F:=E × E))
  exact (adj.clm_apply (contDiff_snd.snd)).sub (contDiff_snd.fst)

theorem smooth {δ:ℝ} (positive:0<δ) (v:E):ContDiff ℝ ∞ (coefficient positive v):=by
  exact (smooth_gradient.inner ℝ contDiff_const).mul
    ((SmoothSeparatedReciprocal.smooth positive).comp (smooth_gradient.inner ℝ smooth_gradient))

theorem coefficient_eq {δ:ℝ} (positive:0<δ) (v:E)
    (p:(E→L[ℝ]E) × (E × E)) (gap:δ≤‖gradient p‖^2):
    coefficient positive v p=⟪gradient p,v⟫/(‖gradient p‖^2):=by
  dsimp only [coefficient]
  rw [real_inner_self_eq_norm_sq,SmoothSeparatedReciprocal.reciprocal positive gap,div_eq_mul_inv]
end LeanShared.SmoothNonstationarySymbol
