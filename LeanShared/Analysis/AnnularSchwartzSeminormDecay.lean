module
public import LeanShared.Analysis.AnnularSchwartzDecay
public import LeanShared.Analysis.PolynomialSchwartzSeminorm

/-! Arbitrary-order frequency gain for the literal finite Schwartz seminorm,
without supplied high-frequency bounds. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.AnnularEllipticSymbol
open FourierSchwartzKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem seminorm_decay (σ : 𝓢(E,ℂ)) (support : HasCompactSupport σ)
    (ε : ℝ) (positive : 0 < ε) (collar : ∀ ξ, ‖ξ‖ < ε → σ ξ=0)
    (n m : ℕ) (r : ℝ) (large : 1 ≤ r) (f : 𝓢(E,ℂ)) :
    r^(2*n)*ObliqueSchwartzDecay.seminorm m
      (ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f) ≤
      (2^m*ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n f))*
        ∫ y, ‖kernel (symbol σ support ε positive collar n) y‖*(1+‖y‖)^m := by
  have estimate := ObliqueSchwartzDecay.seminorm_le
    ((r:ℂ)^(2*n) • ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f) m
    (B := (2^m*ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n f))*
      ∫ y, ‖kernel (symbol σ support ε positive collar n) y‖*(1+‖y‖)^m)
    (mul_nonneg (by positivity) (integral_nonneg fun y=>by positivity)) (fun x=>by
      simp only [smul_apply,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (by linarith : 0<r)]
      nlinarith only [decay σ support ε positive collar n m r large f x])
  simpa only [map_smul_eq_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by linarith : 0<r)] using estimate
end LeanShared.AnnularEllipticSymbol
