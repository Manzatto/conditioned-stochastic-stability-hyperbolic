module
public import LeanShared.Analysis.FourierWordMoments

/-! Integrability of all actual directional moments follows from the exact
inverse Fourier derivative identity and Schwartz integrability. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace LeanShared.FourierWordMoments
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_moment (σ:𝓢(E,ℂ)) (w:List E) :
    Integrable (fun y=>directions w y*(𝓕⁻ σ) y) := by
  let c:ℂ:=(-(2*Real.pi*Complex.I))^w.length
  have nonzero:c≠0:=by
    apply pow_ne_zero
    simp [Real.pi_ne_zero]
  have identity:(fun y=>directions w y*(𝓕⁻ σ) y)=
      fun y=>c⁻¹*(𝓕⁻ (SchwartzJetSpace.wordDerivative w σ)) y:=by
    funext y
    rw [fourierInv_word]
    change directions w y*(𝓕⁻ σ) y=c⁻¹*(c*directions w y*(𝓕⁻ σ) y)
    rw [mul_assoc,inv_mul_cancel_left₀ nonzero]
  rw [identity]
  exact (𝓕⁻ (SchwartzJetSpace.wordDerivative w σ)).integrable.const_mul _
end LeanShared.FourierWordMoments
