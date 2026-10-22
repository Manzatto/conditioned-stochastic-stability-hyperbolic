module
public import LeanShared.Analysis.ScaledNonstationarySymbol
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! The constructed smooth symbols give the exact integration-by-parts
resolution on the actual separated frequency region, including after
physical frequency normalization. -/
public noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace LeanShared.NonstationarySymbolResolution
variable {E ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem resolution (b:OrthonormalBasis ι ℝ E) {δ:ℝ} (positive:0<δ)
    (p:(E→L[ℝ]E) × (E × E)) (gap:δ≤‖SmoothNonstationarySymbol.gradient p‖^2):
    (∑i,⟪SmoothNonstationarySymbol.gradient p,b i⟫*
      SmoothNonstationarySymbol.coefficient positive (b i) p)=1:=by
  let u:=SmoothNonstationarySymbol.gradient p
  have squares:(∑i,⟪u,b i⟫^2)=‖u‖^2:=by
    simpa only [Real.norm_eq_abs,sq_abs] using b.sum_sq_norm_inner_left u
  have nz:‖u‖^2≠0:=(positive.trans_le gap).ne'
  have identity:(∑i,⟪u,b i⟫*SmoothNonstationarySymbol.coefficient positive (b i) p)=
      (∑i,⟪u,b i⟫^2)*SmoothSeparatedReciprocal.function positive ⟪u,u⟫:=by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [SmoothNonstationarySymbol.coefficient,u]
    ring
  rw [identity,squares,real_inner_self_eq_norm_sq,
    SmoothSeparatedReciprocal.reciprocal positive gap,mul_inv_cancel₀ nz]

theorem gradient_smul (A:E→L[ℝ]E) (z:E × E) (s:ℝ):
    SmoothNonstationarySymbol.gradient (A,s • z)=s • SmoothNonstationarySymbol.gradient (A,z):=by
  simp only [SmoothNonstationarySymbol.gradient,Prod.smul_fst,Prod.smul_snd,map_smul,smul_sub]

theorem scaled_resolution (b:OrthonormalBasis ι ℝ E) {δ:ℝ} (positive:0<δ)
    (A:E→L[ℝ]E) (z:E × E) (Λ:ℝ)
    (gap:δ≤‖SmoothNonstationarySymbol.gradient (A,Λ⁻¹ • z)‖^2):
    (∑i,⟪SmoothNonstationarySymbol.gradient (A,z),b i⟫*
      ScaledNonstationarySymbol.function positive (b i) Λ A z)=1:=by
  have raw:=resolution b positive (A,Λ⁻¹ • z) gap
  rw [gradient_smul] at raw
  convert raw using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [ScaledNonstationarySymbol.function,real_inner_smul_left]
  ring
end LeanShared.NonstationarySymbolResolution
