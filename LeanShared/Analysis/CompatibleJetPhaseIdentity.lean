module
public import LeanShared.Analysis.FiniteRegularisedPhaseIdentity
public import LeanShared.Analysis.CompactJetPhysicalKernel
import Mathlib.Tactic

/-! The actual whole-jet convolution supplies the C1 coefficients and
compact supports in the regularized phase identity. No separately chosen
frequency derivatives or smooth approximants are assumed. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution BoundedContinuousFunction
namespace LeanShared.CompatibleJetPhaseIdentity
open NonstationaryPhaseIntegration
variable {E ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  {Z:Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]

omit [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z] in
theorem identity (μ:Measure E) [μ.IsAddHaarMeasure] (n:ℕ) (K:Set Z)
    {κ:E→ℝ} (smoothκ:ContDiff ℝ 1 κ) (compactκ:HasCompactSupport κ)
    (q:ι→E→ᵇ(SupportedFiniteJetSpace.space n K))
    (compactq:∀i,HasCompactSupport (fun w=>q i w))
    {φ:E→ℝ} (hφ:ContDiff ℝ 1 φ) (f:E→ℂ) (v:ι→E) (ζ:Z)
    (resolution:∀w,∑i,(fderiv ℝ φ w (v i):ℂ)*
      SupportedJetFourierEvaluation.physical n K (q i w) ζ=f w)
    (Λ:ℝ) (hΛ:Λ≠0):
    let qr:ι→E→SupportedFiniteJetSpace.space n K:=fun i=>κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun w=>q i w);
    -Complex.I*(∫w,oscillation Λ φ w*f w ∂μ)=
      (Λ:ℂ)⁻¹*(∑i,∫w,oscillation Λ φ w*
        fderiv ℝ (fun w'=>SupportedJetFourierEvaluation.physical n K (qr i w') ζ) w (v i) ∂μ)+
      -Complex.I*(∑i,∫w,oscillation Λ φ w*(fderiv ℝ φ w (v i):ℂ)*
        (SupportedJetFourierEvaluation.physical n K (q i w) ζ-
          SupportedJetFourierEvaluation.physical n K (qr i w) ζ) ∂μ):=by
  intro qr
  let ev:SupportedFiniteJetSpace.space n K→L[ℝ]ℂ:=
    ((BoundedContinuousFunction.evalCLM ℂ ζ).comp
      (SupportedJetFourierEvaluation.physical n K)).restrictScalars ℝ
  have regular (i:ι):ContDiff ℝ 1 (qr i):=
    compactκ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) smoothκ
      ((q i).continuous.locallyIntegrable (μ:=μ))
  apply FiniteRegularisedPhaseIdentity.identity μ hφ f v
    (fun i w=>ev (q i w)) (fun i w=>ev (qr i w))
    (fun i=>ev.continuous.comp (q i).continuous)
    (fun i=>(compactq i).comp_left ev.map_zero)
    (fun i=>ev.contDiff.comp (regular i))
    (fun i=>(CompactJetPhysicalKernel.regularized_compact μ n K compactκ (compactq i)).comp_left ev.map_zero)
    resolution Λ hΛ
end LeanShared.CompatibleJetPhaseIdentity
