module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafAnnularPairing
public import LeanShared.Analysis.ConeAnnularSupport
public import LeanShared.Analysis.FrequencyGainCancellation

/-! Polynomial growth allowed by the actual weighted block norm is overcome
by the proved annular elliptic gain. The resulting pairings decay geometrically. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared LeanShared.FourierSchwartzKernel LeanShared.ConeDyadicSymbols
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

theorem exists_dyadic_block_pairing_bound (U : Submodule ℝ E) (C : Set E)
    (cone : ConeData U C) (b : OrthonormalBasis ι ℝ U)
    {Cplus Cminus : Set E} (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus)
    (q m : ℕ) (order : (Module.finrank ℝ Uᗮ:ℝ)<(m:ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f test : 𝓢(E,ℂ)) (A : ℝ), 0 ≤ A →
      (∀ (j : ℕ × Bool) (Γ : Index U C),
        (∫ x, ‖ConeFourierBlocks.block (symbols χ Φ j) f x‖ ∂inducedVolume U volume Γ.val) ≤
          A*((2:ℝ)^j.1)^q) →
      ∀ j : ℕ × Bool,
        ‖∫ x, ConeFourierBlocks.block (symbols χ Φ j) f x*test x‖ ≤
          (D*A*(ObliqueSchwartzDecay.seminorm m test+
            ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power (q+1) test)))*
            (1/2:ℝ)^j.1 := by
  obtain ⟨B,hB,pairing⟩ := exists_schwartz_pairing_bound U C cone b m order
  obtain ⟨D,hD,annular⟩ := exists_annular_pairing_bound U C cone b χ (q+1) m order
  refine ⟨B+D,add_nonneg hB hD,fun f test A hA leaves j=>?_⟩
  have first : 0 ≤ ObliqueSchwartzDecay.seminorm m test := apply_nonneg _ _
  have second : 0 ≤ ObliqueSchwartzDecay.seminorm m
      (FourierSchwartzLaplacian.power (q+1) test) := apply_nonneg _ _
  by_cases zero : j.1=0
  · have leafBound : ∀ Γ : Index U C,
        (∫ x, ‖ConeFourierBlocks.block (symbols χ Φ j) f x‖ ∂inducedVolume U volume Γ.val) ≤ A := by
      intro Γ
      simpa only [zero,pow_zero,one_pow,mul_one] using leaves j Γ
    have estimate := pairing (ConeFourierBlocks.block (symbols χ Φ j) f) test A leafBound
    rw [zero,pow_zero,mul_one]
    nlinarith only [estimate,mul_nonneg hD hA,mul_nonneg (mul_nonneg hB hA) second,
      mul_nonneg (mul_nonneg hD hA) first,mul_nonneg (mul_nonneg hD hA) second]
  · let σ := ConeHolderAnisotropicEmbedding.highBase χ Φ j.2
    let r : ℝ := 2^j.1
    have hr : 1 ≤ r := one_le_pow₀ (by norm_num)
    have symbolIdentity : symbols χ Φ j=dilateSymbol σ r (by linarith) := by
      simp only [symbols,DyadicSymbols.symbolsFromMultipliers,DyadicSymbols.symbol,
        zero,↓reduceIte]
      rfl
    have leafBound : ∀ Γ : Index U C,
        (∫ x, ‖ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f x‖
          ∂inducedVolume U volume Γ.val) ≤ A*r^q := by
      intro Γ
      rw [← symbolIdentity]
      exact leaves j Γ
    have gain := annular σ f test (A*r^q) r (by positivity) hr
      (ConeHolderAnisotropicEmbedding.high_annulus χ Φ j.2) leafBound
    have estimate := FrequencyGainCancellation.bound q hr (norm_nonneg _) gain
    rw [← symbolIdentity] at estimate
    have inverse : r⁻¹=(1/2:ℝ)^j.1 := by simp only [r,inv_pow,one_div]
    rw [inverse] at estimate
    have positivePower : 0 ≤ (1/2:ℝ)^j.1 := by positivity
    apply estimate.trans
    apply mul_le_mul_of_nonneg_right _ positivePower
    nlinarith only [mul_nonneg (mul_nonneg hB hA) first,
      mul_nonneg (mul_nonneg hB hA) second,mul_nonneg (mul_nonneg hD hA) first]
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
