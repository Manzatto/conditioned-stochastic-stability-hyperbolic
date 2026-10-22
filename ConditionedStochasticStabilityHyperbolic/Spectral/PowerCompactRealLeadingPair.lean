module

public import ConditionedStochasticStabilityHyperbolic.Spectral.GeneralizedSpectralComparison
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProjectorOrientation

import Mathlib.Tactic.Ring

/-! # A precise deferred power-compact spectral-projector source

For a nonzero algebraically simple real eigenvalue of a square-compact operator,
classical Riesz spectral
calculus constructs a normalized bounded real left functional. This source
contract asserts no spectral gap, positivity, quasi-ergodic conclusion or
noise limit. Algebraic simplicity must be proved separately from the analytic
projector and actual generalized spectral correspondence.
-/

@[expose] public noncomputable section
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PowerCompactRealLeadingPair

variable {X : Type*} [MetricSpace X]

/-- The ordinary compact Riesz projector theorem for a real operator and
its actual complexification. Complex conjugation invariance gives the real
normalized pair; algebraic simplicity rules out generalized Jordan vectors.
This is an explicit theorem parameter, not an axiom or noisy gap assumption. -/
def ClassicalContract : Prop :=
  ∀ (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (Q : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)),
    IsCompactOperator (Q ^ 2 : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) →
    (∀ f, Q (AbsorbingMarkovChains.ComplexKernel.ofReal f) =
      AbsorbingMarkovChains.ComplexKernel.ofReal (P f)) →
    ∀ (r : ℝ), 0 < r →
    ∀ f₀ : X →ᵇ ℂ, f₀ ≠ 0 → Q f₀ = (r : ℂ) • f₀ →
    (∀ k : ℕ, ∀ f, ((Q - (r : ℂ) • 1) ^ k) f = 0 →
      ∃ c : ℂ, f = c • f₀) →
    ∃ (g : X →ᵇ ℝ) (μ : (X →ᵇ ℝ) →L[ℝ] ℝ) (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ),
      μ g = 1 ∧
      (∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ)) ∧
      Q (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
        (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g ∧
      (∀ f, ℓ (Q f) = (r : ℂ) * ℓ f)

/-- Common retained generalized comparison and analytic algebraic simplicity
produce the physical pair through the classical compact projector theorem.
The right and left pair are outputs here rather than source hypotheses. -/
theorem exists_pair_of_square_compact_generalized_comparison
    (hRiesz : ClassicalContract (X := X))
    {A W : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (Pa : A →L[ℂ] A) (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (Q : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ))
    (hQ : IsCompactOperator (Q ^ 2 : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)))
    (hcomm : ∀ f, Q (AbsorbingMarkovChains.ComplexKernel.ofReal f) =
      AbsorbingMarkovChains.ComplexKernel.ofReal (P f))
    (a : A →L[ℂ] W) (b : (X →ᵇ ℂ) →L[ℂ] W)
    (r : ℝ) (hr : 0 < r)
    (hcompare : GeneralizedSpectralComparison.Comparison Pa Q a b (r : ℂ))
    (hsep : GeneralizedSpectralComparison.Separates Q b (r : ℂ))
    (γ : A) (f₀ : X →ᵇ ℂ) (hf₀ : f₀ ≠ 0) (heig : Q f₀ = (r : ℂ) • f₀)
    (hident : b f₀ = a γ)
    (hsimple : ∀ k : ℕ, ∀ v, ((Pa - (r : ℂ) • 1) ^ k) v = 0 →
      ∃ c : ℂ, v = c • γ) :
    ∃ (g : X →ᵇ ℝ) (μ : (X →ᵇ ℝ) →L[ℝ] ℝ) (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ),
      μ g = 1 ∧
      (∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ)) ∧
      Q (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
        (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g ∧
      (∀ f, ℓ (Q f) = (r : ℂ) * ℓ f) := by
  exact hRiesz P Q hQ hcomm r hr f₀ hf₀ heig
    (GeneralizedSpectralComparison.generalized_simple Pa Q a b (r : ℂ)
      hcompare hsep γ f₀ heig hident hsimple)

/-- Normalization reorients a one-dimensional complex eigenspace around the
constructed real right function, without assuming its ambient analytic scale. -/
theorem simple_of_span_and_normalized_pair
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f₀ g f : F) (ℓ : F →L[ℂ] ℂ) (hg : ∃ b : ℂ, g = b • f₀)
    (hf : ∃ a : ℂ, f = a • f₀) (hpair : ℓ g = 1) :
    f = ℓ f • g := by
  obtain ⟨b, hgb⟩ := hg
  obtain ⟨a, hfa⟩ := hf
  have hnorm : b * ℓ f₀ = 1 := by simpa only [hgb, map_smul, smul_eq_mul] using hpair
  rw [hgb, hfa, map_smul, smul_eq_mul, smul_smul]
  have he : (a * ℓ f₀) * b = a := by
    calc
      (a * ℓ f₀) * b = a * (b * ℓ f₀) := by ring
      _ = a := by rw [hnorm, mul_one]
  rw [he]

/-- Produce the actual positive canonical gap from compactness, common-region
ordinary/generalized comparisons, analytic dominance and algebraic simplicity.
No physical eigenpair, left law or gap is an input. -/
theorem exists_canonicalGap_of_square_compact_comparison
    (hRiesz : ClassicalContract (X := X))
    (hFredholm : PowerCompactGap.SquareCompactFredholm (F := X →ᵇ ℂ))
    {A W : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (Pa : A →L[ℂ] A) (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (Q : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ))
    (hQ : IsCompactOperator (Q ^ 2 : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)))
    (hcomm : ∀ f, Q (AbsorbingMarkovChains.ComplexKernel.ofReal f) =
      AbsorbingMarkovChains.ComplexKernel.ofReal (P f))
    (hpositive : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P f x)
    (a : A →L[ℂ] W) (b : (X →ᵇ ℂ) →L[ℂ] W)
    (ρ r : ℝ) (hρr : ρ < r) (hr : 0 < r)
    (hordinary : ComparedSpectralGap.EigenvectorComparison Pa Q a b ρ)
    (hcompare : GeneralizedSpectralComparison.Comparison Pa Q a b (r : ℂ))
    (hsep : GeneralizedSpectralComparison.Separates Q b (r : ℂ))
    (γ : A) (f₀ : X →ᵇ ℂ) (hf₀ : f₀ ≠ 0) (heig : Q f₀ = (r : ℂ) • f₀)
    (hident : b f₀ = a γ)
    (hsimple : ∀ k : ℕ, ∀ v, ((Pa - (r : ℂ) • 1) ^ k) v = 0 →
      ∃ c : ℂ, v = c • γ)
    (hbound : ∀ v : A, v ≠ 0 → ∀ z : ℂ, Pa v = z • v → ‖z‖ ≤ r)
    (hperipheral : ∀ v : A, v ≠ 0 → ∀ z : ℂ,
      Pa v = z • v → ‖z‖ = r → z = (r : ℂ)) :
    ∃ d : RankOneSpectralData P (1 : X →ᵇ ℝ), d.rate = r ∧ d.mean 1 = 1 := by
  obtain ⟨g, μ, ℓ, hpair, hreal, hright, hleft⟩ :=
    exists_pair_of_square_compact_generalized_comparison hRiesz Pa P Q hQ hcomm a b r hr
      hcompare hsep γ f₀ hf₀ heig hident hsimple
  have hpairC : ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal g) = 1 := by
    rw [hreal, hpair]
    rfl
  have hgC : AbsorbingMarkovChains.ComplexKernel.ofReal g ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hpairC
    exact zero_ne_one hpairC
  let : Nontrivial (X →ᵇ ℂ) := ⟨⟨AbsorbingMarkovChains.ComplexKernel.ofReal g, 0, hgC⟩⟩
  have hphysical := GeneralizedSpectralComparison.generalized_simple Pa Q a b (r : ℂ)
    hcompare hsep γ f₀ heig hident hsimple
  have hchainG : (Q - (r : ℂ) • 1) (AbsorbingMarkovChains.ComplexKernel.ofReal g) = 0 := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, hright, sub_self]
  have hgs : ∃ c : ℂ, AbsorbingMarkovChains.ComplexKernel.ofReal g = c • f₀ :=
    hphysical 1 _ (by simpa only [pow_one] using hchainG)
  have hsimpleQ : ∀ f, Q f = (r : ℂ) • f →
      ∃ c : ℂ, f = c • AbsorbingMarkovChains.ComplexKernel.ofReal g := by
    intro f hf
    have hchain : (Q - (r : ℂ) • 1) f = 0 := by
      simp only [sub_apply, smul_apply, one_apply_eq_self, hf, sub_self]
    exact ⟨ℓ f, simple_of_span_and_normalized_pair f₀ _ f ℓ hgs
      (hphysical 1 f (by simpa only [pow_one] using hchain)) hpairC⟩
  have hspec := PowerCompactGap.spectralRadius_remainder_lt hFredholm Q hQ r hr
    (AbsorbingMarkovChains.ComplexKernel.ofReal g) ℓ hpairC hright hleft
    (ComparedSpectralGap.eigenvalue_bound Pa Q a b ρ r hρr hordinary hbound)
    (ComparedSpectralGap.peripheral_exclusion Pa Q a b ρ r hρr hordinary hperipheral)
    hsimpleQ
  obtain ⟨_, d, hrate, _, _, hone, _⟩ :=
    ProjectorOrientation.exists_canonicalRankOne_of_complexRadius P r hr g μ Q hcomm
      hpositive ℓ hreal hpair hright hleft hspec
  exact ⟨d, hrate, hone⟩

end ConditionedStochasticStabilityHyperbolic.PowerCompactRealLeadingPair
