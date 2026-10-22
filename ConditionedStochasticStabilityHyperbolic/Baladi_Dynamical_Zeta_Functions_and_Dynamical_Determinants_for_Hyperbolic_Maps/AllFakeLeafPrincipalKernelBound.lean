module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafWeightedLocalizedTransfer
public import LeanShared.Analysis.DyadicSymbols

/-! The actual principal Fourier block has a structural prefactor depending
only on its fixed multiplier bases. The full weight / tangent-Jacobian ratio
stays joint, so no word-length derivative constant enters that prefactor. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype S]

theorem exists_principal_kernel_bound (low high : S → 𝓢(E,ℂ)) :
    ∃ A : ℝ≥0, ∀ (U : Submodule ℝ E) (C D : Set E)
      (sourceCone : ConeData U C) (_targetCone : ConeData U D)
      (μ : Measure U) [μ.IsAddHaarMeasure] (F : OpenPartialHomeomorph E E),
      ContDiffOn ℝ 1 F F.source → ContDiffOn ℝ 1 F.symm F.target → Measurable F →
      ∀ O : Set E, IsOpen O → O ⊆ F.source →
      (∀ Γ : Index U C, Γ.val ⊆ O → ∃ image : Index U D, image.val = F '' Γ.val) →
      ∀ g u : E → ℂ, Measurable g → Measurable u → (∀ x ∉ O, g x = 0) →
      ∀ cost : ℝ≥0, ∀ B : ℝ≥0∞,
      (∀ Δ : Index U D, ∫⁻ y,‖u y‖ₑ ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val ≤ B) →
      (∀ Γ : Index U C, Γ.val ⊆ O →
        let gS := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ.val
          (slope_positive U C sourceCone).le (slope_bound U C sourceCone Γ));
        ∀ v ∈ FakeLeafGraph.parameterDomain U Γ.val, ‖g (gS v)‖ₑ ≤ (cost : ℝ≥0∞)*
          ENNReal.ofReal (((fderiv ℝ F (gS v)).toLinearMap.domRestrict
            (fderiv ℝ gS v).toLinearMap.range).normDet)) →
      ∀ j : ℕ × S, ∀ Γ : Index U C,
      (∫⁻ x,‖∫ w,DyadicSymbols.kernel low high j (x-w)*g w*u (F w)‖ₑ
        ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val) ≤ (A : ℝ≥0∞)*((cost : ℝ≥0∞)*B) := by
  obtain ⟨constant,nonnegative,bound⟩ := DyadicSymbols.exists_uniform_integral_norm_kernel low high
  let A : ℝ≥0 := ⟨constant,nonnegative⟩
  have Aeq : (A : ℝ≥0∞) = ENNReal.ofReal constant := by rw [ENNReal.coe_nnreal_eq]; rfl
  refine ⟨A,?_⟩
  intro U C D sourceCone targetCone μ _ F forward backward measurableF O openO inside images
    g u mg mu supported cost B leafBound jacobian j Γ
  have massBound : (∫⁻ z,‖DyadicSymbols.kernel low high j z‖ₑ) ≤ (A : ℝ≥0∞) := by
    rw [Aeq, ←ofReal_integral_norm_eq_lintegral_enorm (DyadicSymbols.kernel low high j).integrable]
    exact ENNReal.ofReal_le_ofReal (bound j)
  have positiveBound := weighted_convolution_transfer_bound U sourceCone targetCone μ volume F
    forward backward measurableF O openO inside images
    (fun z => ‖DyadicSymbols.kernel low high j z‖ₑ) (fun z => ‖g z‖ₑ) (fun z => ‖u z‖ₑ)
    (DyadicSymbols.kernel low high j).continuous.measurable.enorm mg.enorm mu.enorm
    (fun z hz => by rw [supported z hz,enorm_zero]) cost B leafBound jacobian Γ
  calc
    _ ≤ ∫⁻ x,∫⁻ w,‖DyadicSymbols.kernel low high j (x-w)‖ₑ*(‖g w‖ₑ*‖u (F w)‖ₑ)
        ∂volume ∂EmbeddedSubmanifoldVolume.volume U μ Γ.val := by
      apply lintegral_mono
      intro x
      simpa only [enorm_mul,mul_assoc] using enorm_integral_le_lintegral_enorm
        (fun w => DyadicSymbols.kernel low high j (x-w)*g w*u (F w))
    _ ≤ _ := positiveBound.trans (mul_le_mul_of_nonneg_right massBound bot_le)

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
