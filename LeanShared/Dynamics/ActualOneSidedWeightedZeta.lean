module

public import LeanShared.Dynamics.ActualOneSidedPeriodicAsymptotic
public import LeanShared.Analysis.ExponentiallyAccurateZeta

/-! The literal main graph weighted zeta function has a simple leading
denominator and a nonzero analytic numerator on a strictly larger disk.
Its leading eigenvalue is constructed from the original potential.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
open scoped NNReal ENNReal
variable {A : Type*} [TopologicalSpace A] [Fintype A] {R : A → A → Prop}

/-- The zero coefficient is irrelevant to the logarithmic series; all
positive coefficients are the actual finite periodic weight sums. -/
@[expose] def futurePeriodicCoefficient (ψ : FuturePath R → ℝ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (futurePeriodicWeightSum ψ (n + 1) : ℂ)

@[expose] def futureWeightedZeta (ψ : FuturePath R → ℝ) (z : ℂ) : ℂ :=
  ExponentiallyAccurateZeta.zeta (futurePeriodicCoefficient ψ) z

variable [DiscreteTopology A] [CompactSpace A] [Nonempty (FuturePath R)]

theorem actual_periodic_coefficient_asymptotic (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    0 < (abelRadiusReal ψ)⁻¹ ∧ ∃ κ D : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < D ∧ ∀ n : ℕ,
      ‖futurePeriodicCoefficient ψ n - (((abelRadiusReal ψ)⁻¹ : ℝ) : ℂ) ^ n‖ ≤
        D * ((abelRadiusReal ψ)⁻¹ * κ) ^ n := by
  obtain ⟨positiveρ, κ, D, positiveκ, smallκ, positiveD, relative⟩ :=
    actual_periodic_relative_asymptotic ψ θ Cψ positiveθ smallθ nonnegativeψ potential N connections nextConnections
  let ρ := (abelRadiusReal ψ)⁻¹
  refine ⟨positiveρ, κ, D, positiveκ, smallκ, positiveD, ?_⟩
  intro n
  cases n with
  | zero => simp only [futurePeriodicCoefficient, pow_zero, sub_self, norm_zero, mul_one]; exact positiveD.le
  | succ n =>
    have identity : futurePeriodicWeightSum ψ (n + 1) - ρ ^ (n + 1) =
        ρ ^ (n + 1) * ((ρ ^ (n + 1))⁻¹ * futurePeriodicWeightSum ψ (n + 1) - 1) := by
      have nonzero : ρ ^ (n + 1) ≠ 0 := ne_of_gt (pow_pos positiveρ _)
      field_simp
    change ‖(futurePeriodicWeightSum ψ (n + 1) : ℂ) - (ρ : ℂ) ^ (n + 1)‖ ≤ _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      identity, abs_mul, abs_of_pos (pow_pos positiveρ _)]
    calc
      _ ≤ ρ ^ (n + 1) * (D * κ ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (relative n) (pow_pos positiveρ _).le
      _ = _ := by rw [mul_pow]; ring

theorem actual_main_weighted_zeta_factor (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    0 < (abelRadiusReal ψ)⁻¹ ∧ ∃ r : ℝ≥0, abelRadiusReal ψ < (r : ℝ) ∧ ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (Metric.eball 0 (r : ℝ≥0∞)) ∧ H 0 = 1 ∧
      (∀ z, H z ≠ 0) ∧ ∀ z : ℂ, (abelRadiusReal ψ)⁻¹ * ‖z‖ < 1 →
        futureWeightedZeta ψ z = H z / (1 - (((abelRadiusReal ψ)⁻¹ : ℝ) : ℂ) * z) := by
  obtain ⟨positiveρ, κ, D, positiveκ, smallκ, _, bound⟩ :=
    actual_periodic_coefficient_asymptotic ψ θ Cψ positiveθ smallθ nonnegativeψ potential N connections nextConnections
  obtain ⟨r, larger, H, analyticH, normalizedH, nonzeroH, factor⟩ :=
    ExponentiallyAccurateZeta.factor (futurePeriodicCoefficient ψ) (abelRadiusReal ψ)⁻¹ κ D
      positiveρ positiveκ smallκ bound
  refine ⟨positiveρ, r, ?_, H, analyticH, normalizedH, nonzeroH, factor⟩
  simpa only [one_div, inv_inv] using larger

end LeanShared.BilateralShadowingCoding
