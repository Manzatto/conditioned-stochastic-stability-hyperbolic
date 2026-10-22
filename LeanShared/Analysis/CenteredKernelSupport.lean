module
public import LeanShared.Analysis.CompatiblePhysicalDerivative
public import LeanShared.Analysis.CompactFourierFubini
import Mathlib.Tactic

/-! Physical support of the compatible jets supplies exact restriction
of the full centered Fourier kernel, including arbitrary multipliers. -/
public noncomputable section
open Set MeasureTheory
open scoped FourierTransform ContDiff
namespace LeanShared.CenteredKernelSupport
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {Z:Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]

omit [NormedSpace ℝ E] in
theorem multiplier_restrict (μ:Measure E) (n:ℕ) (K:Set Z)
    (q:E→SupportedFiniteJetSpace.space n K) {L:Set E} (supported:tsupport q⊆L)
    (ψ:E→Z→ℂ) (z:E→Z):
    (∫w,𝓕 (fun ζ=>ψ w ζ*SupportedJetFourierEvaluation.physical n K (q w) ζ) (z w) ∂μ)=
      ∫w in L,𝓕 (fun ζ=>ψ w ζ*SupportedJetFourierEvaluation.physical n K (q w) ζ) (z w) ∂μ:=by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro w hw
  have qw:q w=0:=image_eq_zero_of_notMem_tsupport (fun h=>hw (supported h))
  simp only [qw,map_zero]
  change 𝓕 (fun ζ=>ψ w ζ*0) (z w)=0
  simp [Real.fourier_eq']

omit [MeasurableSpace E] [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z] in
theorem derivative_support (n:ℕ) (K:Set Z)
    (q:E→SupportedFiniteJetSpace.space n K) {L:Set E} (supported:tsupport q⊆L) (v:E):
    tsupport (fun w=>fderiv ℝ q w v)⊆L:=
  (tsupport_fderiv_apply_subset ℝ (f:=q) v).trans supported
end LeanShared.CenteredKernelSupport
