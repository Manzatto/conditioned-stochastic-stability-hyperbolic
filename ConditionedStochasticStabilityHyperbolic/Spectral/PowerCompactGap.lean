module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexGap

/-! # Complementary radius from simple dominant spectrum for compact powers

Square compactness suffices; compactness of the transfer itself is not
assumed. The named classical Fredholm input states only that nonzero spectral
points of an operator with compact square are eigenvalues. Spectral dominance,
peripheral exclusion and simplicity are supplied by cross-space comparison.
The complementary radius and exponential real gap are then conclusions.
-/

@[expose] public noncomputable section

open scoped ENNReal

namespace ConditionedStochasticStabilityHyperbolic.PowerCompactGap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Deferred classical Fredholm theorem for operators with compact square.
This is an operator-independent background contract; it says nothing about
leading eigenvalues, simplicity, positivity or stochastic stability. -/
def SquareCompactFredholm : Prop :=
  ∀ T : F →L[ℂ] F, IsCompactOperator (T ^ 2 : F →L[ℂ] F) →
    ∀ z : ℂ, z ≠ 0 → z ∈ spectrum ℂ T →
      ∃ f : F, f ≠ 0 ∧ T f = z • f

omit [CompleteSpace F] in
/-- Removing an invariant finite-rank projection preserves square compactness. -/
theorem remainder_square_isCompact
    (Q : F →L[ℂ] F) (hQ : IsCompactOperator (Q ^ 2 : F →L[ℂ] F))
    (r : ℝ) (g : F) (ℓ : F →L[ℂ] ℂ)
    (hpair : ℓ g = 1) (hright : Q g = (r : ℂ) • g)
    (hleft : ∀ f, ℓ (Q f) = (r : ℂ) * ℓ f) :
    IsCompactOperator ((AbsorbingMarkovChains.CompactRankOneGap.remainder Q r g ℓ) ^ 2 : F →L[ℂ] F) := by
  have he : (AbsorbingMarkovChains.CompactRankOneGap.remainder Q r g ℓ) ^ 2 =
      AbsorbingMarkovChains.CompactRankOneGap.remainder (Q ^ 2) (r ^ 2) g ℓ := by
    ext f
    rw [pow_two, mul_apply_eq_comp]
    change Q (AbsorbingMarkovChains.CompactRankOneGap.remainder Q r g ℓ f) -
      ℓ (AbsorbingMarkovChains.CompactRankOneGap.remainder Q r g ℓ f) • ((r : ℂ) • g) = _
    rw [AbsorbingMarkovChains.CompactRankOneGap.mean_remainder Q r g ℓ hpair hleft,
      zero_smul, sub_zero]
    change Q (Q f - ℓ f • ((r : ℂ) • g)) =
      (Q ^ 2) f - ℓ f • (((r ^ 2 : ℝ) : ℂ) • g)
    rw [map_sub, map_smul, map_smul, hright, smul_smul, smul_smul, smul_smul,
      Complex.ofReal_pow, pow_two, mul_apply_eq_comp]
    congr 1
    congr 1
    ring
  rw [he]
  exact AbsorbingMarkovChains.CompactRankOneGap.remainder_isCompact (Q ^ 2) hQ (r ^ 2) g ℓ

omit [CompleteSpace F] in
/-- The classical power-compact Fredholm contract and compared eigenvectors
exclude all peripheral spectrum of the complementary operator. -/
theorem norm_mem_spectrum_remainder_lt
    (hFredholm : SquareCompactFredholm (F := F))
    (Q : F →L[ℂ] F) (hQ : IsCompactOperator (Q ^ 2 : F →L[ℂ] F))
    (r : ℝ) (hr : 0 < r) (g : F) (ℓ : F →L[ℂ] ℂ)
    (hpair : ℓ g = 1) (hright : Q g = (r : ℂ) • g)
    (hleft : ∀ f, ℓ (Q f) = (r : ℂ) * ℓ f)
    (hbound : ∀ f : F, f ≠ 0 → ∀ z : ℂ, Q f = z • f → ‖z‖ ≤ r)
    (hperipheral : ∀ f : F, f ≠ 0 → ∀ z : ℂ,
      Q f = z • f → ‖z‖ = r → z = (r : ℂ))
    (hsimple : ∀ f : F, Q f = (r : ℂ) • f → ∃ c : ℂ, f = c • g)
    {z : ℂ} (hz : z ∈ spectrum ℂ
      (AbsorbingMarkovChains.CompactRankOneGap.remainder Q r g ℓ)) : ‖z‖ < r := by
  by_cases hz0 : z = 0
  · simpa [hz0] using hr
  obtain ⟨f, hfne, hf⟩ := hFredholm _
    (remainder_square_isCompact Q hQ r g ℓ hpair hright hleft) z hz0 hz
  have hzero : ℓ f = 0 := by
    have he := congrArg ℓ hf
    rw [AbsorbingMarkovChains.CompactRankOneGap.mean_remainder Q r g ℓ hpair hleft,
      map_smul, smul_eq_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hz0
  have hQf : Q f = z • f := by
    change Q f - ℓ f • ((r : ℂ) • g) = z • f at hf
    simpa only [hzero, zero_smul, sub_zero] using hf
  apply lt_of_le_of_ne (hbound f hfne z hQf)
  intro heq
  have hzr := hperipheral f hfne z hQf heq
  obtain ⟨c, hc⟩ := hsimple f (by rwa [← hzr])
  have hc0 : c = 0 := by simpa only [hc, map_smul, hpair, smul_eq_mul, mul_one] using hzero
  exact hfne (by rw [hc, hc0, zero_smul])

/-- Compactness of the spectrum gives a strict radius uniformly below the
leading eigenvalue. No quantitative geometric decay estimate is assumed. -/
theorem spectralRadius_remainder_lt [Nontrivial F]
    (hFredholm : SquareCompactFredholm (F := F))
    (Q : F →L[ℂ] F) (hQ : IsCompactOperator (Q ^ 2 : F →L[ℂ] F))
    (r : ℝ) (hr : 0 < r) (g : F) (ℓ : F →L[ℂ] ℂ)
    (hpair : ℓ g = 1) (hright : Q g = (r : ℂ) • g)
    (hleft : ∀ f, ℓ (Q f) = (r : ℂ) * ℓ f)
    (hbound : ∀ f : F, f ≠ 0 → ∀ z : ℂ, Q f = z • f → ‖z‖ ≤ r)
    (hperipheral : ∀ f : F, f ≠ 0 → ∀ z : ℂ,
      Q f = z • f → ‖z‖ = r → z = (r : ℂ))
    (hsimple : ∀ f : F, Q f = (r : ℂ) • f → ∃ c : ℂ, f = c • g) :
    spectralRadius ℂ (AbsorbingMarkovChains.CompactRankOneGap.remainder Q r g ℓ) <
      ENNReal.ofReal r := by
  rw [ENNReal.ofReal_eq_coe_nnreal hr.le]
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro z hz
  exact norm_mem_spectrum_remainder_lt hFredholm Q hQ r hr g ℓ hpair hright hleft
    hbound hperipheral hsimple hz

end ConditionedStochasticStabilityHyperbolic.PowerCompactGap
