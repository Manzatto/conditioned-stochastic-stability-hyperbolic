module
public import LeanShared.Analysis.CompactJetPhysicalKernel
import Mathlib.Tactic

/-! Actual physical differentiation commutes with frequency evaluation
on the compatible Banach jet. Its joint continuity and compact support
follow from those of the Banach derivative. -/
public noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff
namespace LeanShared.CompatiblePhysicalDerivative
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Z:Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z] in
theorem formula (n:ℕ) (K:Set Z) {q:E→SupportedFiniteJetSpace.space n K}
    (qc:ContDiff ℝ 1 q) (x v:E) (ζ:Z):
    fderiv ℝ (fun w=>SupportedJetFourierEvaluation.physical n K (q w) ζ) x v=
      SupportedJetFourierEvaluation.physical n K (fderiv ℝ q x v) ζ:=by
  let ev:SupportedFiniteJetSpace.space n K→L[ℝ]ℂ:=
    ((BoundedContinuousFunction.evalCLM ℂ ζ).comp
      (SupportedJetFourierEvaluation.physical n K)).restrictScalars ℝ
  exact congrArg (fun L:E→L[ℝ]ℂ=>L v)
    (ev.hasFDerivAt.comp x ((qc.differentiable (by norm_num) x).hasFDerivAt)).fderiv

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z] in
theorem continuous_joint (n:ℕ) (K:Set Z) {q:E→SupportedFiniteJetSpace.space n K}
    (qc:ContDiff ℝ 1 q) (v:E):
    Continuous (fun p:E × Z=>
      fderiv ℝ (fun w=>SupportedJetFourierEvaluation.physical n K (q w) p.2) p.1 v):=by
  simp_rw [formula n K qc]
  exact CompactJetPhysicalKernel.continuous_physical n K
    ((qc.continuous_fderiv (by norm_num)).clm_apply continuous_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z] in
theorem compact_joint (n:ℕ) {K:Set Z} (compactK:IsCompact K)
    {q:E→SupportedFiniteJetSpace.space n K} (qc:ContDiff ℝ 1 q)
    (qs:HasCompactSupport q) (v:E):
    HasCompactSupport (fun p:E × Z=>
      fderiv ℝ (fun w=>SupportedJetFourierEvaluation.physical n K (q w) p.2) p.1 v):=by
  simp_rw [formula n K qc]
  exact CompactJetPhysicalKernel.compact_physical n compactK
    (q:=fun w=>fderiv ℝ q w v) (qs.fderiv_apply ℝ v)
end LeanShared.CompatiblePhysicalDerivative
