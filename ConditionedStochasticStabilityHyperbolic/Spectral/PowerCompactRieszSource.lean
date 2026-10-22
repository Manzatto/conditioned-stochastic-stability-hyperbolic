module

public import LeanShared.Analysis.SimpleSquareCompactLeft
public import ConditionedStochasticStabilityHyperbolic.Spectral.PowerCompactRealLeadingPair
import Mathlib.Tactic.Push

/-! The real normalized left/right pair is constructed from square compactness
and algebraic simplicity. Hahn–Banach and a finite-rank perturbation suffice;
no Riesz spectral-projector source is required. -/

public noncomputable section
open ContinuousLinearMap
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PowerCompactRealLeadingPair
open AbsorbingMarkovChains.ComplexKernel
variable {X : Type*} [MetricSpace X]

/-- Discharges the real square-compact Riesz-pair source. -/
theorem classicalContract : ClassicalContract (X := X) := by
  intro P Q hQ hcomm r hr f₀ hf₀ heig simple
  have decompose (f : X →ᵇ ℂ) : f = ofReal (AbsorbingMarkovChains.ComplexKernel.realPart f) + Complex.I • ofReal (imagPart f) := by
    ext x
    apply Complex.ext <;> simp
  have realQ (f : X →ᵇ ℂ) : AbsorbingMarkovChains.ComplexKernel.realPart (Q f) = P (AbsorbingMarkovChains.ComplexKernel.realPart f) := by
    conv_lhs => rw [decompose f, map_add, map_smul, hcomm, hcomm]
    ext x
    simp
  have imagQ (f : X →ᵇ ℂ) : imagPart (Q f) = P (imagPart f) := by
    conv_lhs => rw [decompose f, map_add, map_smul, hcomm, hcomm]
    ext x
    simp
  have realEigen : P (AbsorbingMarkovChains.ComplexKernel.realPart f₀) = r • AbsorbingMarkovChains.ComplexKernel.realPart f₀ := by
    rw [← realQ, heig]
    ext x
    simp
  have imagEigen : P (imagPart f₀) = r • imagPart f₀ := by
    rw [← imagQ, heig]
    ext x
    simp
  have realChoice : ∃ g : X →ᵇ ℝ, g ≠ 0 ∧ P g = r • g := by
    by_cases hre : AbsorbingMarkovChains.ComplexKernel.realPart f₀ = 0
    · refine ⟨imagPart f₀, ?_, imagEigen⟩
      intro him
      apply hf₀
      rw [decompose f₀, hre, him, map_zero, smul_zero, add_zero]
    · exact ⟨AbsorbingMarkovChains.ComplexKernel.realPart f₀, hre, realEigen⟩
  obtain ⟨g, hg, hPg⟩ := realChoice
  have embedding_injective : Function.Injective (ofReal (M := X)) := by
    intro f h he
    ext x
    exact Complex.ofReal_injective (congrArg (fun v : X →ᵇ ℂ => v x) he)
  have hgC : ofReal g ≠ 0 := by
    intro he
    exact hg (embedding_injective (by simpa only [map_zero] using he))
  have hQg : Q (ofReal g) = (r : ℂ) • ofReal g := by
    rw [hcomm, hPg, map_smul]
    rfl
  have kernelG : ((Q - (r : ℂ) • 1 : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) ^ 2) (ofReal g) = 0 := by
    rw [pow_two, mul_apply_eq_comp]
    have hh : (Q - (r : ℂ) • 1) (ofReal g) = 0 := by
      simp only [sub_apply, smul_apply, one_apply_eq_self, hQg, sub_self]
    rw [hh, map_zero]
  obtain ⟨b, hb⟩ := simple 2 (ofReal g) kernelG
  have hbne : b ≠ 0 := by intro he; rw [he, zero_smul] at hb; exact hgC hb
  have simpleG : ∀ f : X →ᵇ ℂ, ((Q - (r : ℂ) • 1 : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) ^ 2) f = 0 →
      ∃ c : ℂ, f = c • ofReal g := by
    intro f hf
    obtain ⟨a, ha⟩ := simple 2 f hf
    refine ⟨a / b, ?_⟩
    rw [hb, smul_smul, div_mul_cancel₀ a hbne]
    exact ha
  obtain ⟨ℓ₀, hnorm, hleft⟩ := LeanShared.SimpleSquareCompactLeft.exists_left Q hQ
    (r : ℂ) (by exact_mod_cast hr.ne') (ofReal g) hgC hQg simpleG
  let μ : (X →ᵇ ℝ) →L[ℝ] ℝ := Complex.reCLM.comp ((ℓ₀.restrictScalars ℝ).comp ofReal)
  have hμg : μ g = 1 := by change (ℓ₀ (ofReal g)).re = 1; rw [hnorm]; rfl
  have hμleft (f : X →ᵇ ℝ) : μ (P f) = r * μ f := by
    change (ℓ₀ (ofReal (P f))).re = r * (ℓ₀ (ofReal f)).re
    rw [← hcomm, hleft]
    simp
  let lr : (X →ᵇ ℂ) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (μ.comp AbsorbingMarkovChains.ComplexKernel.realPart) +
      Complex.I • Complex.ofRealCLM.comp (μ.comp imagPart)
  have lr_formula (f : X →ᵇ ℂ) : lr f = (μ (AbsorbingMarkovChains.ComplexKernel.realPart f) : ℂ) + Complex.I * (μ (imagPart f) : ℂ) := rfl
  have real_smul (c : ℂ) (f : X →ᵇ ℂ) :
      AbsorbingMarkovChains.ComplexKernel.realPart (c • f) = c.re • AbsorbingMarkovChains.ComplexKernel.realPart f - c.im • imagPart f := by
    ext x
    simp [Complex.mul_re]
  have imag_smul (c : ℂ) (f : X →ᵇ ℂ) :
      imagPart (c • f) = c.re • imagPart f + c.im • AbsorbingMarkovChains.ComplexKernel.realPart f := by
    ext x
    simp [Complex.mul_im]
  let ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ :=
    { toFun := lr
      map_add' := map_add lr
      map_smul' := by
        intro c f
        change lr (c • f) = c * lr f
        rw [lr_formula, lr_formula, real_smul, imag_smul, map_sub, map_add, map_smul, map_smul,
          map_smul, map_smul]
        simp only [smul_eq_mul]
        push_cast
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      cont := lr.continuous }
  have real_ofReal (f : X →ᵇ ℝ) : AbsorbingMarkovChains.ComplexKernel.realPart (ofReal f) = f := by ext x; rfl
  have imag_ofReal (f : X →ᵇ ℝ) : imagPart (ofReal f) = 0 := by ext x; rfl
  refine ⟨g, μ, ℓ, hμg, ?_, hQg, ?_⟩
  · intro f
    change lr (ofReal f) = (μ f : ℂ)
    rw [lr_formula, real_ofReal, imag_ofReal, map_zero]
    simp
  · intro f
    change lr (Q f) = (r : ℂ) * lr f
    rw [lr_formula, lr_formula, realQ, imagQ, hμleft, hμleft]
    push_cast
    ring

end ConditionedStochasticStabilityHyperbolic.PowerCompactRealLeadingPair
