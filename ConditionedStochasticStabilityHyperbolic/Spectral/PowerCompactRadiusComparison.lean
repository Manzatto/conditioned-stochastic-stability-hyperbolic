module

public import ConditionedStochasticStabilityHyperbolic.Spectral.PowerCompactGap

/-! # Actual power-compact radius bounds from eigenvalue comparison

The classical cross-space input compares individual eigenvalues outside the
analytic essential-radius cutoff. Square compactness and ordinary Fredholm
then produce the physical radius bound, without subordinate mixing or a
supplied physical spectral-radius inequality.
-/

@[expose] public noncomputable section
open scoped ENNReal
namespace ConditionedStochasticStabilityHyperbolic.PowerCompactRadiusComparison
open PowerCompactGap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Nontrivial F]

theorem radius_lt_of_eigenvalue_comparison
    (hFredholm : SquareCompactFredholm (F := F))
    (P : E →L[ℂ] E) (Q : F →L[ℂ] F)
    (hQ : IsCompactOperator (Q ^ 2 : F →L[ℂ] F))
    (α β : ℝ) (hα : 0 ≤ α) (hαβ : α < β)
    (hP : spectralRadius ℂ P < ENNReal.ofReal β)
    (hcompare : ∀ f : F, f ≠ 0 → ∀ z : ℂ, Q f = z • f →
      α < ‖z‖ → z ∈ spectrum ℂ P) : spectralRadius ℂ Q < ENNReal.ofReal β := by
  have hβ : 0 < β := hα.trans_lt hαβ
  rw [ENNReal.ofReal_eq_coe_nnreal hβ.le]
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro z hz
  by_cases hsmall : ‖z‖ ≤ α
  · exact hsmall.trans_lt hαβ
  · have hlarge : α < ‖z‖ := lt_of_not_ge hsmall
    have hzne : z ≠ 0 := by
      intro he
      rw [he, norm_zero] at hlarge
      exact (not_lt_of_ge hα) hlarge
    obtain ⟨f, hf, heig⟩ := hFredholm Q hQ z hzne hz
    have hzP := hcompare f hf z heig hlarge
    have hnorm : (‖z‖₊ : ENNReal) ≤ spectralRadius ℂ P := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂_of_le z hzP le_rfl
    have he : ENNReal.ofReal ‖z‖ < ENNReal.ofReal β := by
      simpa only [ENNReal.coe_nnreal_eq, coe_nnnorm] using hnorm.trans_lt hP
    exact (ENNReal.ofReal_lt_ofReal_iff hβ).mp he

end ConditionedStochasticStabilityHyperbolic.PowerCompactRadiusComparison
