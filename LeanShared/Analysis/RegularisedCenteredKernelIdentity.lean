module
public import LeanShared.Analysis.CenteredKernelLinearIdentity
public import LeanShared.Analysis.CompatibleJetPhaseIdentity
public import LeanShared.Analysis.NonlinearJetResidualFamily
import Mathlib.Tactic

/-! The exact regularized integration-by-parts decomposition for the
centered nonlinear Fourier kernel, before any absolute-value estimate. -/
public noncomputable section
set_option maxHeartbeats 1500000
open Set MeasureTheory
open scoped ContDiff Convolution FourierTransform BoundedContinuousFunction RealInnerProductSpace
namespace LeanShared.RegularisedCenteredKernelIdentity
open HilbertFrequencyPair NonstationaryPhaseIntegration
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)]

theorem identity {ι:Type*} [Fintype ι] (μ:Measure E) [μ.IsAddHaarMeasure]
    (n:ℕ) {K:Set (Space E)} (compactK:IsCompact K)
    {κ:E→ℝ} (smoothκ:ContDiff ℝ 1 κ) (compactκ:HasCompactSupport κ)
    (q:ι→E→ᵇ(SupportedFiniteJetSpace.space n K))
    (compactq:∀i,HasCompactSupport (fun w=>q i w))
    (G:E→E) (smoothG:ContDiff ℝ 1 G) (v:ι→E)
    (a b Λ s t:ℝ) (ha:Λ*s=a) (hb:Λ*t=b) (hΛ:Λ≠0)
    (f:E→Space E→ℂ) (fc:Continuous f.uncurry) (fs:HasCompactSupport f.uncurry)
    (resolution:∀w ζ,∑i,(fderiv ℝ (NonlinearFourierPhaseGradient.phase G
      (s • (decode ζ).1) (t • (decode ζ).2)) w (v i):ℂ)*
      SupportedJetFourierEvaluation.physical n K (q i w) ζ=f w ζ)
    (x y:E):
    let qr:=fun i=>κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun w=>q i w);
    let d:E→Space E→ℂ:=fun w ζ=>∑i,
      fderiv ℝ (fun w'=>SupportedJetFourierEvaluation.physical n K (qr i w') ζ) w (v i);
    let r:E→Space E→ℂ:=fun w ζ=>∑i,
      (fderiv ℝ (NonlinearFourierPhaseGradient.phase G (s • (decode ζ).1) (t • (decode ζ).2)) w (v i):ℂ)*
      SupportedJetFourierEvaluation.physical n K (q i w-qr i w) ζ;
    -Complex.I*(∫w,𝓕 (f w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))) ∂μ)=
      (Λ:ℂ)⁻¹*(∫w,𝓕 (d w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))) ∂μ)+
      -Complex.I*(∫w,𝓕 (r w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))) ∂μ):=by
  intro qr d r
  have regular (i:ι):ContDiff ℝ 1 (qr i):=
    compactκ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) smoothκ
      ((q i).continuous.locallyIntegrable (μ:=μ))
  have compactqr (i:ι):HasCompactSupport (qr i):=
    CompactJetPhysicalKernel.regularized_compact μ n K compactκ (compactq i)
  have dc:Continuous d.uncurry:=by
    apply continuous_finsetSum
    intro i _
    exact CompatiblePhysicalDerivative.continuous_joint n K (regular i) (v i)
  have ds:HasCompactSupport d.uncurry:=by
    convert! HasCompactSupport.finset_sum (s:=Finset.univ)
      (fun i _=>CompatiblePhysicalDerivative.compact_joint n compactK (regular i) (compactqr i) (v i)) using 1
    funext p
    simp only [Finset.sum_apply]
    rfl
  have rc:Continuous r.uncurry:=by
    apply continuous_finsetSum
    intro i _
    exact NonlinearJetResidualFamily.continuous_residual G smoothG s t (v i) n K
      ((q i).continuous.sub (regular i).continuous)
  have rs:HasCompactSupport r.uncurry:=by
    convert! HasCompactSupport.finset_sum (s:=Finset.univ)
      (fun i _=>NonlinearJetResidualFamily.compact_residual G s t (v i) n compactK
        (q:=fun w=>q i w-qr i w) ((compactq i).sub (compactqr i))) using 1
    funext p
    simp only [Finset.sum_apply]
    rfl
  apply CenteredKernelLinearIdentity.transfer μ G smoothG.continuous a b Λ s t ha hb x y
    f d r fc fs dc ds rc rs (-Complex.I) (Λ:ℂ)⁻¹ (-Complex.I)
  intro ζ
  let φ:=NonlinearFourierPhaseGradient.phase G (s • (decode ζ).1) (t • (decode ζ).2)
  have phaseC:ContDiff ℝ 1 φ:=(innerSL ℝ (s • (decode ζ).1)).contDiff.neg.add
    ((innerSL ℝ (t • (decode ζ).2)).contDiff.comp smoothG)
  have phaseEq:φ=(fun w=>-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫):=by
    funext w
    simp only [φ,NonlinearFourierPhaseGradient.phase,real_inner_smul_left]
    ring
  have raw:=CompatibleJetPhaseIdentity.identity μ n K smoothκ compactκ q compactq phaseC
    (fun w=>f w ζ) v ζ (fun w=>resolution w ζ) Λ hΛ
  have dint (i:ι):Integrable (fun w=>oscillation Λ φ w*
      fderiv ℝ (fun w'=>SupportedJetFourierEvaluation.physical n K (qr i w') ζ) w (v i)) μ:=by
    have c:Continuous (fun w=>fderiv ℝ (qr i) w (v i)):=
      ((regular i).continuous_fderiv (by norm_num)).clm_apply continuous_const
    let ev:=((BoundedContinuousFunction.evalCLM ℂ ζ).comp
      (SupportedJetFourierEvaluation.physical n K)).restrictScalars ℝ
    simp_rw [CompatiblePhysicalDerivative.formula n K (regular i)]
    exact ((smooth_oscillation phaseC Λ).continuous.mul (ev.continuous.comp c)).integrable_of_hasCompactSupport
      (((compactqr i).fderiv_apply ℝ (v i)).comp_left ev.map_zero).mul_left
  have rint (i:ι):Integrable (fun w=>oscillation Λ φ w*(fderiv ℝ φ w (v i):ℂ)*
      (SupportedJetFourierEvaluation.physical n K (q i w) ζ-
        SupportedJetFourierEvaluation.physical n K (qr i w) ζ)) μ:=by
    let ev:=((BoundedContinuousFunction.evalCLM ℂ ζ).comp
      (SupportedJetFourierEvaluation.physical n K)).restrictScalars ℝ
    exact RegularisedPhaseIdentity.integrable_directed μ phaseC
      ((ev.continuous.comp (q i).continuous).sub (ev.continuous.comp (regular i).continuous))
      (((compactq i).comp_left ev.map_zero).sub ((compactqr i).comp_left ev.map_zero)) Λ (v i)
  have dEq:(∫w,oscillation Λ φ w*d w ζ ∂μ)=
      ∑i,∫w,oscillation Λ φ w*
        fderiv ℝ (fun w'=>SupportedJetFourierEvaluation.physical n K (qr i w') ζ) w (v i) ∂μ:=by
    simp only [d,Finset.mul_sum]
    exact integral_finsetSum _ (fun i _=>dint i)
  have rEq:(∫w,oscillation Λ φ w*r w ζ ∂μ)=
      ∑i,∫w,oscillation Λ φ w*(fderiv ℝ φ w (v i):ℂ)*
        (SupportedJetFourierEvaluation.physical n K (q i w) ζ-
          SupportedJetFourierEvaluation.physical n K (qr i w) ζ) ∂μ:=by
    simp only [r,Finset.mul_sum,map_sub,BoundedContinuousFunction.sub_apply,mul_assoc]
    exact integral_finsetSum _ (fun i _=>by simpa only [mul_assoc] using rint i)
  dsimp only at raw
  rw [←dEq,←rEq] at raw
  simpa only [phaseEq] using raw
end LeanShared.RegularisedCenteredKernelIdentity
