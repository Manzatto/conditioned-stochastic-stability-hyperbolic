module
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualInvariantCoreAverage

@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.RawRegularAverageRealizations
variable {Reg A F : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem cancel_normalization
    (realize : Reg →L[ℂ] A) (physical : Reg →L[ℂ] F)
    (forward : Reg →L[ℂ] Reg) (P Praw : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (R : ℝ) (hR : 0 < R)
    (hP : P = ((R⁻¹ : ℝ) : ℂ) • Praw)
    (analytic : realize.comp (((R⁻¹ : ℝ) : ℂ) • forward) =
      (((R⁻¹ : ℝ) : ℂ) • Praw).comp realize)
    (physicalLaw : physical.comp (((R⁻¹ : ℝ) : ℂ) • forward) = Q.comp physical) :
    realize.comp forward = ((R : ℂ) • P).comp realize ∧
      physical.comp forward = ((R : ℂ) • Q).comp physical := by
  constructor
  · apply ContinuousLinearMap.ext
    intro v
    have hx : realize (((R⁻¹ : ℝ) : ℂ) • forward v) = P (realize v) :=
      (congrArg (fun L : Reg →L[ℂ] A => L v) analytic).trans
        (congrArg (fun L : A →L[ℂ] A => L (realize v)) hP).symm
    have hs := congrArg (fun x => (R : ℂ) • x) hx
    simpa only [map_smul, smul_smul, Complex.ofReal_inv,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne'), one_smul,
      ContinuousLinearMap.comp_apply, smul_apply] using hs
  · apply ContinuousLinearMap.ext
    intro v
    have hs := congrArg (fun x => (R : ℂ) • x)
      (congrArg (fun L : Reg →L[ℂ] F => L v) physicalLaw)
    simpa only [map_smul, smul_smul, Complex.ofReal_inv,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne'), one_smul,
      ContinuousLinearMap.comp_apply, smul_apply] using hs
end ConditionedStochasticStabilityHyperbolic.RawRegularAverageRealizations
