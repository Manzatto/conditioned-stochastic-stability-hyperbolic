module
public import LeanShared.Analysis.SupportedJetFourierEvaluation
public import LeanShared.Analysis.BanachScaledHolderMollification
import Mathlib.Tactic

/-! Literal coefficient regularization preserves its actual spatial
Fourier envelope. Fixed frequency support and all derivative relations
are retained in the compatible Banach graph. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution FourierTransform BoundedContinuousFunction
namespace LeanShared.SupportedJetRegularizedKernel
variable {Z:Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
  {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem controls (μ:Measure E) [μ.IsAddHaarMeasure] (n:ℕ)
    {K:Set Z} (compactK:IsCompact K)
    {κ:E→ℝ} (smooth:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ)
    (mass:∫y,κ y ∂μ=1) (q:E→ᵇ(SupportedFiniteJetSpace.space n K))
    {a H r:ℝ} (ha:0<a) (hH:0≤H)
    (holder:∀x y,‖q x-q y‖≤H*‖x-y‖^a) (hr:0<r):
    let qr:=BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>q y)
    let C:ℝ:=4^n*((n+1:ℕ)*volume.real K)
    (∀z,ContDiff ℝ 1 (fun x=>SupportedJetFourierEvaluation.evaluation n compactK z (qr x))) ∧
      (∀x z,(1+‖z‖)^n*
        ‖SupportedJetFourierEvaluation.evaluation n compactK z (qr x)-
          SupportedJetFourierEvaluation.evaluation n compactK z (q x)‖≤
          C*(H*(r^a)⁻¹*(∫y,‖κ y‖*‖y‖^a ∂μ))) ∧
      ∀x z v,(1+‖z‖)^n*
        ‖fderiv ℝ (fun w=>SupportedJetFourierEvaluation.evaluation n compactK z (qr w)) x v‖≤
          C*(H*(r*(r^a)⁻¹)*(∫y,‖fderiv ℝ κ y‖*‖y‖^a ∂μ))*‖v‖:=by
  let qr:=BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>q y)
  let C:ℝ:=4^n*((n+1:ℕ)*volume.real K)
  have hC:0≤C:=by dsimp [C];positivity
  have regular:ContDiff ℝ 1 qr:=
    (BanachNormalizedKernelDilation.compact compact hr).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (BanachNormalizedKernelDilation.smooth smooth r)
      (q.continuous.locallyIntegrable (μ:=μ))
  have error:=BanachScaledHolderMollification.scaled_error μ smooth.continuous compact mass q ha hH holder hr
  have derivative:=BanachScaledHolderMollification.scaled_derivative μ smooth compact q ha hH holder hr
  have envelope (s:SupportedFiniteJetSpace.space n K) (z:Z):
      (1+‖z‖)^n*‖SupportedJetFourierEvaluation.evaluation n compactK z s‖≤C*‖s‖:=by
    rw [SupportedJetFourierEvaluation.evaluation_eq]
    exact SupportedJetFourierEvaluation.polynomial_bound n compactK s z
  refine ⟨?_,?_,?_⟩
  · intro z
    exact (SupportedJetFourierEvaluation.evaluation n compactK z).restrictScalars ℝ |>.contDiff.comp regular
  · intro x z
    rw [←map_sub]
    exact (envelope (qr x-q x) z).trans (mul_le_mul_of_nonneg_left (error x) hC)
  · intro x z v
    let ev:SupportedFiniteJetSpace.space n K→L[ℝ]ℂ:=
      (SupportedJetFourierEvaluation.evaluation n compactK z).restrictScalars ℝ
    have formula:fderiv ℝ (fun w=>ev (qr w)) x v=ev (fderiv ℝ qr x v):=
      congrArg (fun L:E→L[ℝ]ℂ=>L v) (ev.hasFDerivAt.comp x
        ((regular.differentiable (by norm_num) x).hasFDerivAt)).fderiv
    change (1+‖z‖)^n*‖fderiv ℝ (fun w=>ev (qr w)) x v‖≤_
    rw [formula]
    exact (envelope (fderiv ℝ qr x v) z).trans
      ((mul_le_mul_of_nonneg_left ((fderiv ℝ qr x).le_opNorm v) hC).trans
        ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (derivative x) (norm_nonneg v)) hC).trans_eq
          (mul_assoc _ _ _).symm))
end LeanShared.SupportedJetRegularizedKernel
