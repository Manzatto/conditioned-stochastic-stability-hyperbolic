module

public import LeanShared.Dynamics.OneSidedPeriodicWindowEstimate
public import LeanShared.Analysis.GeometricWindowBalance

/-! Actual normalized periodic orbit weights have leading coefficient
one and an exponentially decaying remainder.  The proof uses the literal
Ruelle operator, cylinder-periodic bijection, and graph connections.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

omit [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] in
theorem realizedPrefix_card_bound (m : ℕ) :
    (Fintype.card (RealizedPrefix R m) : ℝ) ≤ (Fintype.card A : ℝ) ^ (m + 1) := by
  have finiteBound : Fintype.card (RealizedPrefix R m) ≤ Fintype.card A ^ (m + 1) := by
    have injective : Function.Injective (fun w : RealizedPrefix R m => w.val) :=
      fun a b equal => Subtype.ext equal
    have bound := Fintype.card_le_of_injective _ injective
    simpa only [Fintype.card_fun, Fintype.card_fin] using bound
  exact_mod_cast finiteBound

variable [Nonempty (FuturePath R)]

theorem actualRuelle_periodic_exponential_asymptotic (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    ∃ κ D : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < D ∧ ∀ n : ℕ,
      |futurePeriodicWeightSum ψ (n + 1) - 1| ≤ D * κ ^ (n + 1) := by
  obtain ⟨τ, C, positiveτ, smallτ, positiveC, diagonal⟩ :=
    actualRuelle_cylinder_diagonal_bound ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital N connections nextConnections
  let E := Cψ * θ / (1 - θ)
  let K := Real.exp E * (1 + (Fintype.card (RealizedPrefix R 0) : ℝ) * 2 * C)
  let J := (Real.exp E * E) * K
  let B := (Fintype.card A : ℝ) * 2 * C
  let b := (Fintype.card A : ℝ) * θ⁻¹
  have nonnegativeE : 0 ≤ E := by dsimp [E]; positivity
  have nonnegativeK : 0 ≤ K := by dsimp [K]; positivity
  have nonnegativeJ : 0 ≤ J := by dsimp [J]; positivity
  have nonnegativeB : 0 ≤ B := by dsimp [B]; positivity
  have nonnegativeb : 0 ≤ b := by dsimp [b]; positivity
  obtain ⟨κ, D, positiveκ, smallκ, nonnegativeD, balanced⟩ :=
    GeometricWindowBalance.bound θ τ b J B positiveθ smallθ positiveτ.le smallτ nonnegativeb nonnegativeJ nonnegativeB
  refine ⟨κ, D + 1, positiveκ, smallκ, by linarith, ?_⟩
  intro n
  obtain ⟨m, window⟩ := balanced (n + 1)
  have uniformBound : futurePeriodicWeightSum ψ (n + 1) ≤ K :=
    periodicWeightSum_uniform_bound ψ θ Cψ τ C positiveθ.le smallθ nonnegativeψ potential
      positiveτ.le smallτ.le positiveC.le diagonal (n + 1)
  have comparison := periodicWeightSum_window_error ψ θ Cψ τ C K positiveθ.le smallθ nonnegativeψ
    potential diagonal (n + 1) m uniformBound
  have cylinderCost : (Fintype.card (RealizedPrefix R m) : ℝ) * (2 * θ⁻¹ ^ m) * C * τ ^ (n + 1) ≤
      B * b ^ m * τ ^ (n + 1) := by
    calc
      _ ≤ (Fintype.card A : ℝ) ^ (m + 1) * (2 * θ⁻¹ ^ m) * C * τ ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (realizedPrefix_card_bound (R := R) m) (by positivity)) positiveC.le) (by positivity)
      _ = _ := by dsimp [B, b]; rw [pow_succ, mul_pow]; ring
  calc
    _ ≤ J * θ ^ m + B * b ^ m * τ ^ (n + 1) := comparison.trans (add_le_add le_rfl cylinderCost)
    _ ≤ D * κ ^ (n + 1) := window
    _ ≤ (D + 1) * κ ^ (n + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end LeanShared.BilateralShadowingCoding
