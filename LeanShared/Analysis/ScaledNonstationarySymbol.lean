module
public import LeanShared.Analysis.NonstationarySymbolHolderBounds
import Mathlib.Tactic

/-! Exact physical frequency scaling of the constructed smooth symbol.
Every frequency derivative retains its actual inverse scale power. -/
public noncomputable section
open scoped ContDiff
namespace LeanShared.ScaledNonstationarySymbol
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

@[expose] def function {δ:ℝ} (positive:0<δ) (v:E) (Λ:ℝ)
    (A:E→L[ℝ]E) (z:E × E):ℝ:=
  Λ⁻¹*SmoothNonstationarySymbol.coefficient positive v (A,Λ⁻¹ • z)

theorem smooth_frequency {δ:ℝ} (positive:0<δ) (v:E) (Λ:ℝ) (A:E→L[ℝ]E):
    ContDiff ℝ ∞ (function positive v Λ A):=by
  exact contDiff_const.mul ((SmoothNonstationarySymbol.smooth positive v).comp
    (contDiff_const.prodMk (contDiff_id.const_smul Λ⁻¹)))

theorem derivative_formula {δ:ℝ} (positive:0<δ) (v:E) (Λ:ℝ)
    (A:E→L[ℝ]E) (z:E × E) (n:ℕ):
    iteratedFDeriv ℝ n (function positive v Λ A) z=
      (Λ⁻¹)^(n+1) • SmoothPartialDerivativeBounds.frequencyDerivative n
        (SmoothNonstationarySymbol.coefficient positive v) (A,Λ⁻¹ • z):=by
  let f:E × E→ℝ:=fun w=>SmoothNonstationarySymbol.coefficient positive v (A,w)
  have regular:ContDiff ℝ ∞ f:=
    (SmoothNonstationarySymbol.smooth positive v).comp (contDiff_const.prodMk contDiff_id)
  have scaledRegular:ContDiff ℝ ∞ (fun w=>f (Λ⁻¹ • w)):=
    regular.comp (contDiff_id.const_smul Λ⁻¹)
  change iteratedFDeriv ℝ n (fun w=>Λ⁻¹ • f (Λ⁻¹ • w)) z=_
  rw [iteratedFDeriv_const_smul_apply' (scaledRegular.of_le (by simp)).contDiffAt]
  rw [congrFun (iteratedFDeriv_comp_const_smul Λ⁻¹ (regular.of_le (by simp))) z]
  rw [smul_smul,←pow_succ']
  rfl

theorem derivative_bound {δ D Z:ℝ} (positive:0<δ) (hD:0≤D) (hZ:0≤Z)
    (v:E) (n:ℕ):
    ∃B L:ℝ,0≤B ∧ 0≤L ∧
      (∀Λ:ℝ,0<Λ→∀A:E→L[ℝ]E,‖A‖≤D→∀z:E × E,‖Λ⁻¹ • z‖≤Z→
        ‖iteratedFDeriv ℝ n (function positive v Λ A) z‖≤(Λ⁻¹)^(n+1)*B) ∧
      ∀Λ:ℝ,0<Λ→∀A A':E→L[ℝ]E,‖A‖≤D→‖A'‖≤D→∀z:E × E,‖Λ⁻¹ • z‖≤Z→
        ‖iteratedFDeriv ℝ n (function positive v Λ A) z-
          iteratedFDeriv ℝ n (function positive v Λ A') z‖≤
          (Λ⁻¹)^(n+1)*L*‖A-A'‖:=by
  obtain ⟨B,L,hB,hL,value,lip⟩:=NonstationarySymbolHolderBounds.compact_bounds positive hD hZ v n
  refine ⟨B,L,hB,hL,?_,?_⟩
  · intro Λ hΛ A hA z hz
    rw [derivative_formula,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (value A hA _ hz) (by positivity)
  · intro Λ hΛ A A' hA hA' z hz
    rw [derivative_formula,derivative_formula,←smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (lip A A' hA hA' _ hz) (by positivity)).trans_eq
      (mul_assoc _ _ _).symm
end LeanShared.ScaledNonstationarySymbol
