module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComparedSpectralGap

/-! # Spectral comparison through a retained region

Restriction need only separate vectors in the leading eigenspace. It need
not be injective on all continuous functions, nor identify eigenfunctions
outside the region where the two weights agree.
-/

@[expose] public noncomputable section

namespace ConditionedStochasticStabilityHyperbolic.RestrictedSpectralComparison

variable {A F W : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Kernel separation is required only on one eigenspace. -/
def SeparatesEigenspace (Q : F →L[ℂ] F) (b : F →L[ℂ] W) (z : ℂ) : Prop :=
  ∀ f, Q f = z • f → b f = 0 → f = 0

theorem leading_eigenvector_simple
    (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (a : A →L[ℂ] W) (b : F →L[ℂ] W) (ρ r : ℝ)
    (hρr : ρ < r) (hr : 0 < r)
    (hcompare : ComparedSpectralGap.EigenvectorComparison P Q a b ρ)
    (hsep : SeparatesEigenspace Q b (r : ℂ))
    (γ : A) (g : F) (hright : Q g = (r : ℂ) • g) (hident : b g = a γ)
    (hsimple : ∀ v : A, P v = (r : ℂ) • v → ∃ c : ℂ, v = c • γ)
    (f : F) (he : Q f = (r : ℂ) • f) : ∃ c : ℂ, f = c • g := by
  by_cases hf : f = 0
  · exact ⟨0, by rw [hf, zero_smul]⟩
  have hnorm : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_of_nonneg hr.le]
  obtain ⟨v, _, hv, hfv⟩ := hcompare f hf (r : ℂ) he (by rwa [hnorm])
  obtain ⟨c, hc⟩ := hsimple v hv
  refine ⟨c, sub_eq_zero.mp (hsep (f - c • g) ?_ ?_)⟩
  · rw [map_sub, map_smul, he, hright, smul_sub, smul_comm c]
  · rw [map_sub, map_smul, hfv, hc, map_smul, hident, sub_self]

theorem complementary_radius_lt [CompleteSpace F] [Nontrivial F]
    (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (a : A →L[ℂ] W) (b : F →L[ℂ] W) (ρ r : ℝ)
    (hρr : ρ < r) (hr : 0 < r)
    (hcompare : ComparedSpectralGap.EigenvectorComparison P Q a b ρ)
    (hsep : SeparatesEigenspace Q b (r : ℂ))
    (hFredholm : PowerCompactGap.SquareCompactFredholm (F := F))
    (hQ : IsCompactOperator (Q ^ 2 : F →L[ℂ] F))
    (γ : A) (g : F) (hident : b g = a γ) (ℓ : F →L[ℂ] ℂ)
    (hpair : ℓ g = 1) (hright : Q g = (r : ℂ) • g)
    (hleft : ∀ f, ℓ (Q f) = (r : ℂ) * ℓ f)
    (hbound : ∀ v : A, v ≠ 0 → ∀ z : ℂ, P v = z • v → ‖z‖ ≤ r)
    (hperipheral : ∀ v : A, v ≠ 0 → ∀ z : ℂ,
      P v = z • v → ‖z‖ = r → z = (r : ℂ))
    (hsimple : ∀ v : A, P v = (r : ℂ) • v → ∃ c : ℂ, v = c • γ) :
    spectralRadius ℂ (AbsorbingMarkovChains.CompactRankOneGap.remainder Q r g ℓ) <
      ENNReal.ofReal r := by
  exact PowerCompactGap.spectralRadius_remainder_lt hFredholm Q hQ r hr g ℓ
    hpair hright hleft
    (ComparedSpectralGap.eigenvalue_bound P Q a b ρ r hρr hcompare hbound)
    (ComparedSpectralGap.peripheral_exclusion P Q a b ρ r hρr hcompare hperipheral)
    (leading_eigenvector_simple P Q a b ρ r hρr hr hcompare hsep γ g hright hident hsimple)

/-- When the actual density already makes the physical transfer compact,
Mathlib's compact Fredholm theory discharges the spectral background step. -/
theorem complementary_radius_lt_of_compact [CompleteSpace F] [Nontrivial F]
    (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (a : A →L[ℂ] W) (b : F →L[ℂ] W) (ρ r : ℝ)
    (hρr : ρ < r) (hr : 0 < r)
    (hcompare : ComparedSpectralGap.EigenvectorComparison P Q a b ρ)
    (hsep : SeparatesEigenspace Q b (r : ℂ))
    (hQ : IsCompactOperator Q)
    (γ : A) (g : F) (hident : b g = a γ) (ℓ : F →L[ℂ] ℂ)
    (hpair : ℓ g = 1) (hright : Q g = (r : ℂ) • g)
    (hleft : ∀ f, ℓ (Q f) = (r : ℂ) * ℓ f)
    (hbound : ∀ v : A, v ≠ 0 → ∀ z : ℂ, P v = z • v → ‖z‖ ≤ r)
    (hperipheral : ∀ v : A, v ≠ 0 → ∀ z : ℂ,
      P v = z • v → ‖z‖ = r → z = (r : ℂ))
    (hsimple : ∀ v : A, P v = (r : ℂ) • v → ∃ c : ℂ, v = c • γ) :
    spectralRadius ℂ (AbsorbingMarkovChains.CompactRankOneGap.remainder Q r g ℓ) <
      ENNReal.ofReal r := by
  exact AbsorbingMarkovChains.CompactRankOneGap.spectralRadius_remainder_lt Q hQ hr g ℓ
    hpair hleft
    (ComparedSpectralGap.eigenvalue_bound P Q a b ρ r hρr hcompare hbound)
    (ComparedSpectralGap.peripheral_exclusion P Q a b ρ r hρr hcompare hperipheral)
    (leading_eigenvector_simple P Q a b ρ r hρr hr hcompare hsep γ g hright hident hsimple)

end ConditionedStochasticStabilityHyperbolic.RestrictedSpectralComparison
