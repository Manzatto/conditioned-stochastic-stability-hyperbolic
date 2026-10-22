module
public import LeanShared.Analysis.CompatiblePhysicalDerivative
public import LeanShared.Analysis.NonlinearFourierPhaseGradient
public import LeanShared.Analysis.HilbertFrequencyPair
import Mathlib.Tactic

/-! The residual directional-gradient times the actual compatible
frequency jet is a jointly continuous compact kernel. Only C1 spatial
regularity of the nonlinear map is used. -/
public noncomputable section
open Set
open scoped ContDiff RealInnerProductSpace
namespace LeanShared.NonlinearJetResidualFamily
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem continuous_direction (G:E→E) (smooth:ContDiff ℝ 1 G) (s t:ℝ) (v:E):
    Continuous (fun p:E × Space E=>
      (fderiv ℝ (NonlinearFourierPhaseGradient.phase G (s • (decode p.2).1)
        (t • (decode p.2).2)) p.1 v:ℂ)):=by
  simp_rw [NonlinearFourierPhaseGradient.derivative (smooth.differentiable (by norm_num) _)]
  have cd:Continuous (fun p:E × Space E=>fderiv ℝ G p.1):=
    (smooth.continuous_fderiv (by norm_num)).comp continuous_fst
  have adj:Continuous (fun p:E × Space E=>(fderiv ℝ G p.1).adjoint):=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.continuous.comp cd
  exact Complex.continuous_ofReal.comp
    (((adj.clm_apply (continuous_const.smul ((decode (E:=E)).continuous.comp continuous_snd).snd)).sub
      (continuous_const.smul ((decode (E:=E)).continuous.comp continuous_snd).fst)).inner continuous_const)

omit [FiniteDimensional ℝ E] in
theorem compact_residual (G:E→E) (s t:ℝ) (v:E) (n:ℕ)
    {K:Set (Space E)} (compactK:IsCompact K)
    {q:E→SupportedFiniteJetSpace.space n K} (qs:HasCompactSupport q):
    HasCompactSupport (fun p:E × Space E=>
      (fderiv ℝ (NonlinearFourierPhaseGradient.phase G (s • (decode p.2).1)
        (t • (decode p.2).2)) p.1 v:ℂ)*SupportedJetFourierEvaluation.physical n K (q p.1) p.2):=
  (CompactJetPhysicalKernel.compact_physical n compactK (q:=q) qs).mul_left

theorem continuous_residual (G:E→E) (smooth:ContDiff ℝ 1 G) (s t:ℝ) (v:E) (n:ℕ)
    (K:Set (Space E)) {q:E→SupportedFiniteJetSpace.space n K} (qc:Continuous q):
    Continuous (fun p:E × Space E=>
      (fderiv ℝ (NonlinearFourierPhaseGradient.phase G (s • (decode p.2).1)
        (t • (decode p.2).2)) p.1 v:ℂ)*SupportedJetFourierEvaluation.physical n K (q p.1) p.2):=
  (continuous_direction G smooth s t v).mul (CompactJetPhysicalKernel.continuous_physical n K qc)
end LeanShared.NonlinearJetResidualFamily
