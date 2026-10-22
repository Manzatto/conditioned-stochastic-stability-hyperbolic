module

public import LeanShared.Analysis.ConditionedOperators
public import AbsorbingMarkovChains.OperatorCesaro
import Mathlib.Tactic.Linarith

/-!
# The rank-one spectral input for conditioned averages

This is the operator part of `lem:spectral_gap_QEM`, with time window
`0,...,n-1`, survival power `n`, and normalization `mean eigenvector = 1`.
-/

@[expose] public noncomputable section

open Filter Finset
open scoped Topology

namespace ConditionedStochasticStabilityHyperbolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Precisely the normalized leading spectral data consumed by the averaging
argument. No neighborhood irreducibility, aperiodicity or probability law is
part of this structure, and the eigenfunctional need not have unit mass. -/
structure RankOneSpectralData (P : E →L[ℝ] E) (one : E) where
  rate : ℝ
  rate_pos : 0 < rate
  mean : E →L[ℝ] ℝ
  eigenvector : E
  mean_eigenvector : mean eigenvector = 1
  mean_one_pos : 0 < mean one
  right_eigenvector : P eigenvector = rate • eigenvector
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  decay : ℝ
  decay_nonneg : 0 ≤ decay
  decay_lt_one : decay < 1
  power_gap : ∀ n : ℕ,
    ‖(rate⁻¹ • P) ^ n - mean.smulRight eigenvector‖ ≤ errorConstant * decay ^ n

namespace RankOneSpectralData

variable {P : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one)

/-- The transfer operator divided by its positive leading eigenvalue. -/
def normalizedOperator : E →L[ℝ] E := d.rate⁻¹ • P

/-- The rank-one limit, in the paper's eigenmeasure/eigenfunction normalization. -/
def projection : E →L[ℝ] E := d.mean.smulRight d.eigenvector

theorem normalized_eigenvector : d.normalizedOperator d.eigenvector = d.eigenvector := by
  simp [normalizedOperator, d.right_eigenvector, smul_smul,
    inv_mul_cancel₀ d.rate_pos.ne']

theorem tendsto_powers :
    Tendsto (fun n : ℕ => d.normalizedOperator ^ n) atTop (𝓝 d.projection) := by
  exact LeanShared.ConditionedOperators.tendsto_powers_of_geometric_gap
    d.normalizedOperator d.projection d.decay_nonneg d.decay_lt_one d.power_gap

/-- The paper's exact operator ratio converges to the eigenvector/eigenmeasure
product. Scalar eigenvalue normalization cancels exactly, rather than only
asymptotically. The eigenfunctional's mass is not required to equal one. -/
theorem tendsto_conditionedAverage (A : E →L[ℝ] E) (ev : E →L[ℝ] ℝ)
    (hx : 0 < ev d.eigenvector) :
    Tendsto (LeanShared.ConditionedOperators.conditionedAverage P A ev one)
      atTop (𝓝 (d.mean (A d.eigenvector))) := by
  let Q := d.normalizedOperator
  let R := d.projection
  let U := ‖R‖ + d.errorConstant
  have hU : 0 ≤ U := add_nonneg (norm_nonneg R) d.errorConstant_nonneg
  have hR : ‖R‖ ≤ U := le_add_of_nonneg_right d.errorConstant_nonneg
  have hQ (n : ℕ) : ‖Q ^ n‖ ≤ U := by
    calc
      ‖Q ^ n‖ ≤ ‖Q ^ n - R‖ + ‖R‖ := by
        simpa only [sub_add_cancel] using norm_add_le (Q ^ n - R) R
      _ ≤ d.errorConstant * d.decay ^ n + ‖R‖ :=
        add_le_add (d.power_gap n) le_rfl
      _ ≤ U := by
        dsimp [U]
        nlinarith [pow_le_one₀ (n := n) d.decay_nonneg d.decay_lt_one.le]
  have havg := AbsorbingMarkovChains.OperatorCesaro.tendsto_operator_average
    Q R (A * Q) d.errorConstant_nonneg hU d.decay_nonneg d.decay_lt_one
    hR hQ d.power_gap
  have hratio := LeanShared.ConditionedOperators.tendsto_conditionedAverage_of_limits
    Q A d.mean ev d.eigenvector one d.normalized_eigenvector
    (mul_pos d.mean_one_pos hx).ne' d.tendsto_powers havg
  apply hratio.congr' (Eventually.of_forall fun n => ?_)
  exact LeanShared.ConditionedOperators.conditionedAverage_smul d.rate⁻¹
    (inv_ne_zero d.rate_pos.ne') P A ev one n

/-- The normalized survival denominator is positive for sufficiently long
times at every starting-state evaluation positive on the eigenvector. -/
theorem eventually_pos_normalized_survival (ev : E →L[ℝ] ℝ)
    (hx : 0 < ev d.eigenvector) :
    ∀ᶠ n : ℕ in atTop, 0 < ev ((d.normalizedOperator ^ n) one) := by
  exact LeanShared.ConditionedOperators.eventually_pos_survival
    d.normalizedOperator d.mean ev d.eigenvector one
    (mul_pos d.mean_one_pos hx) d.tendsto_powers

/-- The constant observation has limit one in the paper's pairing normalization. -/
theorem tendsto_conditionedAverage_one (ev : E →L[ℝ] ℝ)
    (hx : 0 < ev d.eigenvector) :
    Tendsto (LeanShared.ConditionedOperators.conditionedAverage P 1 ev one)
      atTop (𝓝 1) := by
  simpa only [one_apply_eq_self, d.mean_eigenvector] using
    d.tendsto_conditionedAverage (1 : E →L[ℝ] E) ev hx

end RankOneSpectralData

end ConditionedStochasticStabilityHyperbolic
