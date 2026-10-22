module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComparedSpectralGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseSpectralGap

/-! # From anisotropic eigenvalue separation to the literal noisy QEM

This theorem connects the compared analytic spectrum to the actual killed
kernel. Its classical inputs are square-compact Fredholm theory and the
shared-ambient eigenvector comparison. It derives the complementary radius,
geometric real gap, positivity, finite leading measure and full measurable
quasi-ergodic property. The manifold operator realization and its analytic
spectral data are constructed in other modules.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.ComparedNoiseQEM

variable {X A W : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A compared, simple dominant analytic eigenvalue supplies the actual
bounded-measurable QEM; no continuous-space spectral gap is assumed. -/
theorem exists_quasiErgodic
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (P : A →L[ℂ] A) (a : A →L[ℂ] W) (b : (X →ᵇ ℂ) →L[ℂ] W)
    (hb : Function.Injective b) (ρ r : ℝ) (hρr : ρ < r) (hr : 0 < r)
    (hFredholm : PowerCompactGap.SquareCompactFredholm (F := X →ᵇ ℂ))
    (hcompact : IsCompactOperator
      ((ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) ^ 2 :
        (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)))
    (hcompare : ComparedSpectralGap.EigenvectorComparison P
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) a b ρ)
    (γ : A) (g : X →ᵇ ℝ)
    (hident : b (AbsorbingMarkovChains.ComplexKernel.ofReal g) = a γ)
    (μ : (X →ᵇ ℝ) →L[ℝ] ℝ) (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ)
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ))
    (hpair : μ g = 1) (hmass : 0 < μ 1)
    (hright : ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
      (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hleft : ∀ f, ℓ (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF f) = (r : ℂ) * ℓ f)
    (hbound : ∀ v : A, v ≠ 0 → ∀ z : ℂ, P v = z • v → ‖z‖ ≤ r)
    (hperipheral : ∀ v : A, v ≠ 0 → ∀ z : ℂ,
      P v = z • v → ‖z‖ = r → z = (r : ℂ))
    (hsimple : ∀ v : A, P v = (r : ℂ) • v → ∃ c : ℂ, v = c • γ) :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧
      (∀ f : X →ᵇ ℝ, μ f = ∫ x, f x ∂ν) ∧
      C.IsQuasiErgodic (LeanShared.eigenvectorMeasure ν g) := by
  have hpairC : ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal g) = 1 := by
    rw [hreal, hpair]
    rfl
  have hgC : AbsorbingMarkovChains.ComplexKernel.ofReal g ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hpairC
    exact zero_ne_one hpairC
  let : Nontrivial (X →ᵇ ℂ) := ⟨⟨AbsorbingMarkovChains.ComplexKernel.ofReal g, 0, hgC⟩⟩
  have hspec := ComparedSpectralGap.complementary_radius_lt P
    (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) a b ρ r hρr hcompare
    hFredholm hcompact hb hr γ (AbsorbingMarkovChains.ComplexKernel.ofReal g)
    hident ℓ hpairC hright hleft hbound hperipheral hsimple
  exact NoiseSpectralGap.exists_quasiErgodic_of_complementaryRadius C hSF
    r hr g μ ℓ hreal hpair hmass hright hleft hspec

end ConditionedStochasticStabilityHyperbolic.ComparedNoiseQEM
