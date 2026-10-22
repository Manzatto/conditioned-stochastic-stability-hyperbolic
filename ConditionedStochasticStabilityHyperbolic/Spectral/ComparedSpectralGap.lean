module

public import ConditionedStochasticStabilityHyperbolic.Spectral.PowerCompactGap

/-! # Transporting leading spectral separation between functional spaces

The comparison input identifies eigenvectors in a shared ambient space only
above a fixed essential-radius cutoff. Analytic dominance, peripheral
exclusion and simplicity then transfer to the continuous space. In
combination with square compactness this yields a strict complementary
radius; the exponential estimate is not an input.
-/

@[expose] public noncomputable section

namespace ConditionedStochasticStabilityHyperbolic.ComparedSpectralGap

variable {A F W : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Exact eigenvector comparison above the common essential-radius cutoff.
The shared ambient embeddings express equality of distributions, without
postulating a bounded map between the two different Banach norms. -/
def EigenvectorComparison
    (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (a : A →L[ℂ] W) (b : F →L[ℂ] W) (ρ : ℝ) : Prop :=
  ∀ f : F, f ≠ 0 → ∀ z : ℂ, Q f = z • f → ρ < ‖z‖ →
    ∃ v : A, v ≠ 0 ∧ P v = z • v ∧ b f = a v

variable (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (a : A →L[ℂ] W) (b : F →L[ℂ] W)
    (ρ r : ℝ) (hρr : ρ < r)
    (hcompare : EigenvectorComparison P Q a b ρ)

include hρr hcompare

/-- Eigenvalues below the comparison cutoff are already subordinate; those
above it inherit the analytic leading bound. -/
theorem eigenvalue_bound
    (hbound : ∀ v : A, v ≠ 0 → ∀ z : ℂ, P v = z • v → ‖z‖ ≤ r)
    (f : F) (hf : f ≠ 0) (z : ℂ) (he : Q f = z • f) : ‖z‖ ≤ r := by
  by_cases hz : ρ < ‖z‖
  · obtain ⟨v, hv, hvz, _⟩ := hcompare f hf z he hz
    exact hbound v hv z hvz
  · exact (le_of_not_gt hz).trans hρr.le

/-- The peripheral eigenvalue on the analytic space also excludes peripheral
cycles on the continuous space, without positivity irreducibility. -/
theorem peripheral_exclusion
    (hperipheral : ∀ v : A, v ≠ 0 → ∀ z : ℂ,
      P v = z • v → ‖z‖ = r → z = (r : ℂ))
    (f : F) (hf : f ≠ 0) (z : ℂ) (he : Q f = z • f) (hz : ‖z‖ = r) :
    z = (r : ℂ) := by
  obtain ⟨v, hv, hvz, _⟩ := hcompare f hf z he (by rwa [hz])
  exact hperipheral v hv z hvz hz

/-- Equality in the common ambient space transports one-dimensionality of
the leading eigenspace. -/
theorem leading_eigenvector_simple
    (hb : Function.Injective b) (hr : 0 < r)
    (γ : A) (g : F) (hident : b g = a γ)
    (hsimple : ∀ v : A, P v = (r : ℂ) • v → ∃ c : ℂ, v = c • γ)
    (f : F) (he : Q f = (r : ℂ) • f) : ∃ c : ℂ, f = c • g := by
  by_cases hf : f = 0
  · exact ⟨0, by rw [hf, zero_smul]⟩
  have hnorm : ‖(r : ℂ)‖ = r := by simp [Complex.norm_real, Real.norm_of_nonneg hr.le]
  obtain ⟨v, _, hv, hfv⟩ := hcompare f hf (r : ℂ) he (by rwa [hnorm])
  obtain ⟨c, hc⟩ := hsimple v hv
  refine ⟨c, hb ?_⟩
  rw [hfv, hc, map_smul, map_smul, hident]

/-- Cross-space eigenvector comparison and square compactness produce the
strict continuous-space complementary radius from analytic eigenvalue data. -/
theorem complementary_radius_lt [CompleteSpace F] [Nontrivial F]
    (hFredholm : PowerCompactGap.SquareCompactFredholm (F := F))
    (hQ : IsCompactOperator (Q ^ 2 : F →L[ℂ] F))
    (hb : Function.Injective b) (hr : 0 < r)
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
    (eigenvalue_bound P Q a b ρ r hρr hcompare hbound)
    (peripheral_exclusion P Q a b ρ r hρr hcompare hperipheral)
    (leading_eigenvector_simple P Q a b ρ r hρr hcompare hb hr γ g hident hsimple)

end ConditionedStochasticStabilityHyperbolic.ComparedSpectralGap
