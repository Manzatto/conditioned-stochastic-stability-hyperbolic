module
public import LeanShared.Analysis.AnnularEllipticDilation
public import LeanShared.Analysis.SchwartzWeightedConvolution

/-! Actual high-frequency polynomial decay of test blocks, with arbitrarily
large frequency gain derived from the constructed elliptic parametrix. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.AnnularEllipticSymbol
open FourierSchwartzKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem decay (σ : 𝓢(E,ℂ)) (support : HasCompactSupport σ)
    (ε : ℝ) (positive : 0 < ε) (collar : ∀ ξ, ‖ξ‖ < ε → σ ξ=0)
    (n m : ℕ) (r : ℝ) (large : 1 ≤ r) (f : 𝓢(E,ℂ)) (x : E) :
    r^(2*n)*((1+‖x‖)^m*‖ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f x‖) ≤
      (2^m*ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n f))*
        ∫ y, ‖kernel (symbol σ support ε positive collar n) y‖*(1+‖y‖)^m := by
  have identity := congrArg (fun g : 𝓢(E,ℂ) => ‖g x‖)
    (reconstruct_dilated σ support ε positive collar n r (by linarith) f)
  simp only [smul_apply,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by linarith : 0<r)] at identity
  have bound := SchwartzWeightedConvolution.dilated_bound
    (symbol σ support ε positive collar n) (FourierSchwartzLaplacian.power n f) m large x
  rw [identity] at bound
  nlinarith only [bound]
end LeanShared.AnnularEllipticSymbol
