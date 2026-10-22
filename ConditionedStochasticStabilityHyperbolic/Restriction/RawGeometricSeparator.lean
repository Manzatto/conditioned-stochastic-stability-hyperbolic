module

public import ConditionedStochasticStabilityHyperbolic.Restriction.GeometricSpectralRestriction
public import ConditionedStochasticStabilityHyperbolic.Spectral.GeneralizedSpectralComparison

/-! # Raw spectral separation from actual geometric extinction

Scalar normalization and a faithful distribution embedding of the retained
functions do not require globally injective restriction. The actual geometric
small-noise theorem supplies the generalized separator in the KL consumer.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem scaled_separator_of_restriction
    {Y : Type*} [TopologicalSpace Y]
    (P : (Y →ᵇ ℂ) →L[ℂ] (Y →ᵇ ℂ)) (V : Set Y)
    (c : (V →ᵇ ℂ) →L[ℂ] Z) (hc : Function.Injective c)
    (s z : ℂ) (hs : s ≠ 0)
    (hsep : ∀ k : ℕ, ∀ f : Y →ᵇ ℂ,
      ((P - (s⁻¹ * z) • 1) ^ k) f = 0 → restrictObservable V f = 0 → f = 0) :
    GeneralizedSpectralComparison.Separates (s • P) (c.comp (restrictObservable V)) z := by
  intro k f hf hb
  apply hsep k f
  · have he : s • P - z • (1 : (Y →ᵇ ℂ) →L[ℂ] (Y →ᵇ ℂ)) =
        s • (P - (s⁻¹ * z) • 1) := by
      rw [smul_sub, smul_smul, mul_inv_cancel_left₀ hs]
    rw [he, smul_pow, smul_apply] at hf
    exact (smul_eq_zero.mp hf).resolve_left (pow_ne_zero _ hs)
  · apply hc
    rw [map_zero]
    exact hb

theorem exists_geometric_raw_separator
    {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U)
    (hcore : LeanShared.isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ LeanShared.forwardTrapped T K ⊆ U)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (w : K → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw W hW hwW
      ∀ (hSF : HasStrongFellerKernel C)
        (c : (retainedRegion K U →ᵇ ℂ) →L[ℂ] Z), Function.Injective c →
        ∀ s z : ℂ, s ≠ 0 → z ≠ 0 →
          GeneralizedSpectralComparison.Separates
            (s • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
            (c.comp (restrictObservable (retainedRegion K U))) z := by
  obtain ⟨δ, hδ, hcert⟩ := exists_geometric_restriction_and_lifting
    T K U hK hU hcore hUK hsep ρ w hw W hW hwW (𝕜 := ℂ)
  refine ⟨δ, hδ, ?_⟩
  intro F hF hclose
  dsimp only
  intro hSF c hc s z hs hz
  have hnormalized := (hcert F hF hclose hSF (s⁻¹ * z)
    (mul_ne_zero (inv_ne_zero hs) hz)).1
  exact scaled_separator_of_restriction _ (retainedRegion K U) c hc s z hs hnormalized

end ConditionedStochasticStabilityHyperbolic.Restriction
