module

public import LeanShared.Dynamics.BilateralPeriodicFutureEquivalence
public import LeanShared.Dynamics.ActualOneSidedWeightedZeta

/-! The original bilateral symbolic weighted zeta has the actual Ruelle
leading factor.  Periodic restriction is bijective and the explicit
future cohomology preserves every literal periodic orbit weight.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
open scoped NNReal ENNReal
variable {A : Type*} [TopologicalSpace A] [Fintype A] {R : A → A → Prop}

@[expose] def bilateralPeriodicWeightSum (φ : Path R → ℝ) (n : ℕ) [NeZero n] : ℝ :=
  ∑ p : PeriodicBilateral (R := R) n, Real.exp (orbitSum (shift R) φ n p.val)

@[expose] def bilateralPeriodicCoefficient (φ : Path R → ℝ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (bilateralPeriodicWeightSum φ (n + 1) : ℂ)

@[expose] def bilateralWeightedZeta (φ : Path R → ℝ) (z : ℂ) : ℂ :=
  ExponentiallyAccurateZeta.zeta (bilateralPeriodicCoefficient φ) z

theorem bilateralPeriodicWeightSum_eq_future (φ : Path R → ℝ)
    (variation : HasExponentialVariations φ) (n : ℕ) [NeZero n] :
    bilateralPeriodicWeightSum φ n = futurePeriodicWeightSum (oneSidedPotential φ) n := by
  unfold bilateralPeriodicWeightSum futurePeriodicWeightSum
  rw [← Equiv.sum_comp (periodicBilateralFutureEquiv n (Nat.pos_of_ne_zero (NeZero.ne n)))
    (fun p : PeriodicFuture (R := R) n => Real.exp (orbitSum futureShift (oneSidedPotential φ) n p.val))]
  exact Finset.sum_congr rfl (fun p _ => oneSidedPotential_periodic_weight φ variation n p.val p.property)

theorem bilateralPeriodicCoefficient_eq_future (φ : Path R → ℝ)
    (variation : HasExponentialVariations φ) :
    bilateralPeriodicCoefficient φ = futurePeriodicCoefficient (oneSidedPotential φ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact congrArg Complex.ofReal (bilateralPeriodicWeightSum_eq_future φ variation (n + 1))

theorem bilateralWeightedZeta_eq_future (φ : Path R → ℝ)
    (variation : HasExponentialVariations φ) (z : ℂ) :
    bilateralWeightedZeta φ z = futureWeightedZeta (oneSidedPotential φ) z := by
  unfold bilateralWeightedZeta futureWeightedZeta
  rw [bilateralPeriodicCoefficient_eq_future φ variation]

variable [DiscreteTopology A] [CompactSpace A] [Nonempty (FuturePath R)]

@[expose] def bilateralRuelleFuturePotential (φ : C(Path R, ℝ))
    (variation : HasExponentialVariations φ) : C(FuturePath R, ℝ) :=
  ⟨oneSidedPotential φ, oneSidedPotential_continuous φ φ.continuous variation⟩

theorem actual_bilateral_weighted_zeta_factor (φ : C(Path R, ℝ))
    (variation : HasExponentialVariations φ)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    0 < (abelRadiusReal (bilateralRuelleFuturePotential φ variation))⁻¹ ∧
      ∃ r : ℝ≥0, abelRadiusReal (bilateralRuelleFuturePotential φ variation) < (r : ℝ) ∧
        ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (Metric.eball 0 (r : ℝ≥0∞)) ∧ H 0 = 1 ∧
          (∀ z, H z ≠ 0) ∧ ∀ z : ℂ,
            (abelRadiusReal (bilateralRuelleFuturePotential φ variation))⁻¹ * ‖z‖ < 1 →
            bilateralWeightedZeta φ z = H z /
              (1 - (((abelRadiusReal (bilateralRuelleFuturePotential φ variation))⁻¹ : ℝ) : ℂ) * z) := by
  obtain ⟨θ, positiveθ, smallθ, Cψ, nonnegativeψ, potential⟩ :=
    oneSidedPotential_exponential φ φ.continuous variation
  obtain ⟨positiveρ, r, larger, H, analyticH, normalizedH, nonzeroH, factor⟩ :=
    actual_main_weighted_zeta_factor (bilateralRuelleFuturePotential φ variation) θ Cψ
      positiveθ smallθ nonnegativeψ potential N connections nextConnections
  refine ⟨positiveρ, r, larger, H, analyticH, normalizedH, nonzeroH, ?_⟩
  intro z small
  rw [bilateralWeightedZeta_eq_future φ variation]
  exact factor z small

end LeanShared.BilateralShadowingCoding
