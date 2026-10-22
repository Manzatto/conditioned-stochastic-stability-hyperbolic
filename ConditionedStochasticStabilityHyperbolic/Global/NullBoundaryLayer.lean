module

public import ConditionedStochasticStabilityHyperbolic.Global.RestrictedLayerChain
public import LeanShared.Probability.KernelEigenmeasureDensity
import Mathlib.Tactic.FieldSimp

/-!
# Closed-layer growth passes to disjoint strata across null boundaries

Noise absolute continuity removes a reference-null boundary from every
transition law. Restriction and one-step smoothing then relate the actual
closed-layer transfer to the actual disjoint-stratum transfer in both
directions. Growth bounds pass without assuming a continuous extension of
arbitrary stratum observables or an indicator coordinate isomorphism.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction ENNReal

namespace ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryLayer

open ComplexStrongFeller LayerOperators

variable {X 𝕜 : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [RCLike 𝕜]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U)

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- Actual transition absolute continuity is enough to delete a null boundary. -/
theorem boundary_mass_zero (σ : Measure X) (hnull : σ Uᶜ = 0)
    (hac : ∀ x, C.killedTransition x ≪ σ) :
    ∀ x, C.killedTransition x Uᶜ = 0 := fun x => hac x hnull

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- The classical actual transition-density formula supplies the null-boundary
certificate without a separately assumed path-support condition. -/
theorem boundary_mass_zero_of_density (σ : Measure X) (q : X × X → ℝ≥0∞)
    (htransition : ∀ x, C.killedTransition x = σ.withDensity (fun y => q (x, y)))
    (hnull : σ Uᶜ = 0) : ∀ x, C.killedTransition x Uᶜ = 0 := by
  intro x
  rw [htransition x]
  exact withDensity_absolutelyContinuous σ (fun y => q (x, y)) hnull

/-- On a conull stratum the original transfer factors through restriction
and smoothing, even when stratum observables do not extend continuously. -/
theorem transfer_eq_extension_restriction
    (hzero : ∀ x, C.killedTransition x Uᶜ = 0) :
    transferOperator (𝕜 := 𝕜) C hSF =
      (extensionOperator C hSF U hU).comp (restrictOperator (𝕜 := 𝕜) U) := by
  ext f x
  rw [transferOperator_apply, ContinuousLinearMap.comp_apply, extensionOperator_apply]
  apply integral_congr_ae
  have ha : ∀ᵐ y ∂C.killedTransition x, y ∈ U := by
    rw [ae_iff]
    exact hzero x
  filter_upwards [ha] with y hy
  exact (zeroExtend_coe U (restrictOperator U f) ⟨y, hy⟩).symm

section Factor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (P : E →L[𝕜] E) (Q : F →L[𝕜] F) (R : E →L[𝕜] F) (S : F →L[𝕜] E)
  (hP : P = S.comp R) (hQ : Q = R.comp S)

include hP hQ in
/-- The stratum powers are smoothed closed-layer powers between the actual
bounded maps. The exceptional time zero is handled separately. -/
theorem factor_pow_succ (n : ℕ) : Q ^ (n + 1) = R.comp ((P ^ n).comp S) := by
  induction n with
  | zero =>
      rw [hQ]
      ext f
      rfl
  | succ n ih =>
      rw [pow_succ, ih, hQ]
      ext f
      simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
      have he : S (R (S f)) = P (S f) := by rw [hP]; rfl
      rw [he, pow_succ, mul_apply_eq_comp]

include hP hQ in
theorem exists_power_bound_of_factor {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ)
    (hbound : ∀ n : ℕ, ‖P ^ n‖ ≤ a * ρ ^ n) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ n : ℕ, ‖Q ^ n‖ ≤ b * ρ ^ n := by
  let b := ‖(1 : F →L[𝕜] F)‖ + ‖R‖ * a * ‖S‖ / ρ
  have hc : 0 ≤ ‖R‖ * a * ‖S‖ := mul_nonneg (mul_nonneg (norm_nonneg _) ha) (norm_nonneg _)
  refine ⟨b, add_nonneg (norm_nonneg _) (div_nonneg hc hρ.le), ?_⟩
  intro n
  cases n with
  | zero =>
      simp only [pow_zero, mul_one]
      exact le_add_of_nonneg_right (div_nonneg hc hρ.le)
  | succ n =>
      rw [factor_pow_succ P Q R S hP hQ]
      have hb : ‖R.comp ((P ^ n).comp S)‖ ≤ ‖R‖ * a * ‖S‖ * ρ ^ n := by
        calc
          _ ≤ ‖R‖ * ‖(P ^ n).comp S‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖R‖ * (‖P ^ n‖ * ‖S‖) := mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
          _ ≤ ‖R‖ * ((a * ρ ^ n) * ‖S‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)) (norm_nonneg _)
          _ = _ := by ring
      have he : ‖R‖ * a * ‖S‖ * ρ ^ n = (‖R‖ * a * ‖S‖ / ρ) * ρ ^ (n + 1) := by
        rw [pow_succ]
        field_simp
      exact hb.trans (he ▸ mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (norm_nonneg (1 : F →L[𝕜] F))) (pow_nonneg hρ.le _))

end Factor

/-- Closed-layer power growth transfers to the literal Borel-stratum chain.
The raw weight normalization factor can be arbitrary, including larger than one. -/
theorem exists_stratum_power_bound (b : ℝ)
    (hzero : ∀ x, C.killedTransition x Uᶜ = 0)
    {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ)
    (hbound : ∀ n : ℕ, ‖(b • transferOperator (𝕜 := 𝕜) C hSF) ^ n‖ ≤ a * ρ ^ n) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := 𝕜) (RestrictedLayerChain.chain C U hU)
        (RestrictedLayerChain.strongFeller C hSF U hU)) ^ n‖ ≤ c * ρ ^ n := by
  rw [RestrictedLayerChain.transferOperator_eq_lower C hSF U hU]
  apply exists_power_bound_of_factor (b • transferOperator (𝕜 := 𝕜) C hSF)
    (b • lowerOperator (𝕜 := 𝕜) C hSF U hU) (restrictOperator (𝕜 := 𝕜) U)
    (b • extensionOperator C hSF U hU) _ _ ha hρ hbound
  · rw [transfer_eq_extension_restriction C hSF U hU hzero]
    ext f
    rfl
  · ext f x
    rfl

/-- In particular the closed-layer estimate can be used directly with actual
noise densities and a reference-null removed boundary. -/
theorem exists_stratum_power_bound_of_density (b : ℝ)
    (σ : Measure X) (q : X × X → ℝ≥0∞)
    (htransition : ∀ x, C.killedTransition x = σ.withDensity (fun y => q (x, y)))
    (hnull : σ Uᶜ = 0)
    {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ)
    (hbound : ∀ n : ℕ, ‖(b • transferOperator (𝕜 := 𝕜) C hSF) ^ n‖ ≤ a * ρ ^ n) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := 𝕜) (RestrictedLayerChain.chain C U hU)
        (RestrictedLayerChain.strongFeller C hSF U hU)) ^ n‖ ≤ c * ρ ^ n :=
  exists_stratum_power_bound C hSF U hU b
    (boundary_mass_zero_of_density C U σ q htransition hnull) ha hρ hbound

end ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryLayer
