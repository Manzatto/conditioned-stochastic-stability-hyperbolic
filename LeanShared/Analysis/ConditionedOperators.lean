module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Operator ratios for conditioned time averages

The powers on either side of the observation add to `n`, with observations
at times `0,...,n-1`. No probability law or spectral-gap theorem is assumed
implicitly. The limit theorem takes operator convergence as explicit input.
-/

@[expose] public noncomputable section

open Filter Finset
open scoped Topology

namespace LeanShared.ConditionedOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The transfer-operator numerator for the time window `0,...,n-1`. -/
def operatorAverage (Q A : E →L[ℝ] E) (n : ℕ) : E →L[ℝ] E :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, Q ^ i * A * Q ^ (n - i)

/-- Evaluation of the averaged operator divided by the matching survival term. -/
def conditionedAverage (Q A : E →L[ℝ] E) (ev : E →L[ℝ] ℝ) (one : E)
    (n : ℕ) : ℝ :=
  ev (operatorAverage Q A n one) / ev ((Q ^ n) one)

/-- Exact indexing bridge to the operator Cesàro formula with powers totaling `n-1`.
The final transition is absorbed into the observation operator `A * Q`. -/
theorem operatorAverage_eq_predecessorAverage (Q A : E →L[ℝ] E) (n : ℕ) :
    operatorAverage Q A n =
      (n : ℝ)⁻¹ • ∑ i ∈ range n, Q ^ i * (A * Q) * Q ^ (n - 1 - i) := by
  unfold operatorAverage
  congr 1
  apply sum_congr rfl
  intro i hi
  have hexp : n - i = (n - 1 - i) + 1 := by
    have := mem_range.mp hi
    omega
  rw [hexp, pow_succ']
  simp only [mul_assoc]

/-- A scalar change of the transfer operator multiplies each numerator by the
same `n`-th power as the survival denominator. -/
theorem operatorAverage_smul (c : ℝ) (Q A : E →L[ℝ] E) (n : ℕ) :
    operatorAverage (c • Q) A n = c ^ n • operatorAverage Q A n := by
  unfold operatorAverage
  have hsum : (∑ i ∈ range n, (c • Q) ^ i * A * (c • Q) ^ (n - i)) =
      c ^ n • ∑ i ∈ range n, Q ^ i * A * Q ^ (n - i) := by
    rw [smul_sum]
    apply sum_congr rfl
    intro i hi
    simp only [smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [← pow_add, Nat.sub_add_cancel (mem_range.mp hi).le]
  rw [hsum, smul_comm]

/-- Nonzero scalar normalization cancels exactly, including at time zero. -/
theorem conditionedAverage_smul (c : ℝ) (hc : c ≠ 0)
    (Q A : E →L[ℝ] E) (ev : E →L[ℝ] ℝ) (one : E) (n : ℕ) :
    conditionedAverage (c • Q) A ev one n = conditionedAverage Q A ev one n := by
  unfold conditionedAverage
  rw [operatorAverage_smul, smul_pow]
  simp only [smul_apply, map_smul, smul_eq_mul]
  exact mul_div_mul_left _ _ (pow_ne_zero n hc)

/-- The paper's conditional ratio limit without requiring `μ one = 1`.
The mass `μ one` and the starting-state coefficient cancel in the quotient. -/
theorem tendsto_conditionedAverage_of_limits (Q A : E →L[ℝ] E)
    (μ ev : E →L[ℝ] ℝ) (η one : E)
    (hη : Q η = η) (hden : μ one * ev η ≠ 0)
    (hpow : Tendsto (fun n : ℕ => Q ^ n) atTop (𝓝 (μ.smulRight η)))
    (havg : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ range n, Q ^ i * (A * Q) * Q ^ (n - 1 - i))
      atTop (𝓝 (μ.smulRight η * (A * Q) * μ.smulRight η))) :
    Tendsto (conditionedAverage Q A ev one) atTop (𝓝 (μ (A η))) := by
  let P := μ.smulRight η
  let V := ev.comp (ContinuousLinearMap.apply ℝ E one)
  have hnum := V.continuous.continuousAt.tendsto.comp havg
  have hsurvival := V.continuous.continuousAt.tendsto.comp hpow
  have hVP : V P = μ one * ev η := by
    simp [V, P, smul_eq_mul]
  have hVAPA : V (P * (A * Q) * P) = μ (A η) * (μ one * ev η) := by
    simp [V, P, mul_apply_eq_comp, hη, smul_eq_mul]
    ring
  change Tendsto _ _ (𝓝 (V (P * (A * Q) * P))) at hnum
  change Tendsto _ _ (𝓝 (V P)) at hsurvival
  rw [hVAPA] at hnum
  rw [hVP] at hsurvival
  have hratio := hnum.div hsurvival hden
  rw [mul_div_cancel_right₀ _ hden] at hratio
  apply hratio.congr' (Eventually.of_forall fun n => ?_)
  change ev (((n : ℝ)⁻¹ • ∑ i ∈ range n,
    Q ^ i * (A * Q) * Q ^ (n - 1 - i)) one) / ev ((Q ^ n) one) =
    ev (operatorAverage Q A n one) / ev ((Q ^ n) one)
  rw [operatorAverage_eq_predecessorAverage]

/-- Positive limiting survival coefficient makes the denominator positive
eventually; division does not rely on an arbitrary zero-denominator convention. -/
theorem eventually_pos_survival (Q : E →L[ℝ] E) (μ ev : E →L[ℝ] ℝ)
    (η one : E) (hden : 0 < μ one * ev η)
    (hpow : Tendsto (fun n : ℕ => Q ^ n) atTop (𝓝 (μ.smulRight η))) :
    ∀ᶠ n : ℕ in atTop, 0 < ev ((Q ^ n) one) := by
  let V := ev.comp (ContinuousLinearMap.apply ℝ E one)
  have h := V.continuous.continuousAt.tendsto.comp hpow
  have heq : V (μ.smulRight η) = μ one * ev η := by
    simp [V, smul_eq_mul]
  rw [heq] at h
  exact h.eventually (lt_mem_nhds hden)

/-- A geometric bound on the operator error gives convergence of the powers. -/
theorem tendsto_powers_of_geometric_gap (Q P : E →L[ℝ] E) {C θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hgap : ∀ n : ℕ, ‖Q ^ n - P‖ ≤ C * θ ^ n) :
    Tendsto (fun n : ℕ => Q ^ n) atTop (𝓝 P) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hgap (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul C)

end LeanShared.ConditionedOperators
