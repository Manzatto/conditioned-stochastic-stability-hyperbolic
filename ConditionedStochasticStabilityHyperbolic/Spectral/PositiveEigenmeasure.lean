module

public import LeanShared.Probability.PositiveFunctionalMeasure
public import ConditionedStochasticStabilityHyperbolic.Spectral.Normalization
import Mathlib.Tactic.Push

/-!
# Constructing the leading measure from positivity

A positive transfer and the given rank-one power gap force its right vector
and left functional to be nonnegative. On a compact live-state space, the
classical Riesz theorem then constructs a finite measure representing the
functional. Thus the actual noisy-process QEM consumer needs no independent
measure-representation hypothesis. Spectral-gap existence and basic-set
support/strict positivity are not proved in this module.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

variable {X : Type*} [MetricSpace X]
  {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)} (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
  (hP : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P f x)

include hP in
theorem normalizedOperator_nonneg (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    0 ≤ d.normalizedOperator f x := by
  rw [normalizedOperator, smul_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr d.rate_pos.le) (hP f hf x)

include hP in
theorem normalized_powers_nonneg (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : X) :
    0 ≤ ((d.normalizedOperator ^ n) f) x := by
  induction n generalizing x with
  | zero => simpa using hf x
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact d.normalizedOperator_nonneg hP _ ih x

include hP in
theorem projection_nonneg (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    0 ≤ d.mean f * d.eigenvector x := by
  let V : (((X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))) →L[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (ContinuousLinearMap.apply ℝ (X →ᵇ ℝ) f)
  have hlim := V.continuous.continuousAt.tendsto.comp d.tendsto_powers
  have hV : V d.projection = d.mean f * d.eigenvector x := by
    simp only [V, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      projection, ContinuousLinearMap.smulRight_apply,
      BoundedContinuousFunction.evalCLM_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul]
  change Tendsto (fun n => ((d.normalizedOperator ^ n) f) x) atTop (𝓝 (V d.projection)) at hlim
  rw [hV] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => d.normalized_powers_nonneg hP f hf n x)

include hP in
theorem eigenvector_nonneg_of_positive (x : X) : 0 ≤ d.eigenvector x :=
  (mul_nonneg_iff_of_pos_left d.mean_one_pos).mp
    (d.projection_nonneg hP 1 (fun _ => zero_le_one) x)

include hP in
theorem exists_eigenvector_pos_of_positive : ∃ x, 0 < d.eigenvector x := by
  by_contra hn
  push Not at hn
  have hz : d.eigenvector = 0 := by
    ext x
    exact le_antisymm (hn x) (d.eigenvector_nonneg_of_positive hP x)
  have hm := d.mean_eigenvector
  rw [hz, map_zero] at hm
  exact zero_ne_one hm

include hP in
theorem mean_nonneg_of_positive (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ d.mean f := by
  obtain ⟨x, hx⟩ := d.exists_eigenvector_pos_of_positive hP
  exact (mul_nonneg_iff_of_pos_right hx).mp (d.projection_nonneg hP f hf x)

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual finite regular leading measure, rather than a supplied witness. -/
def eigenmeasure : Measure X :=
  LeanShared.PositiveFunctionalMeasure.measure d.mean (d.mean_nonneg_of_positive hP)

instance eigenmeasure_isFinite : IsFiniteMeasure (d.eigenmeasure hP) := by
  unfold eigenmeasure
  infer_instance

instance eigenmeasure_regular : (d.eigenmeasure hP).Regular := by
  unfold eigenmeasure
  infer_instance

theorem eigenmeasure_represents (f : X →ᵇ ℝ) :
    d.mean f = ∫ x, f x ∂d.eigenmeasure hP :=
  (LeanShared.PositiveFunctionalMeasure.integral_measure d.mean
    (d.mean_nonneg_of_positive hP) f).symm

end ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

namespace ConditionedStochasticStabilityHyperbolic.RestrictedQuasiErgodic

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
  (F : X × Ω → X) (hF : Measurable F) (U : Set X) [CompactSpace U] (hU : MeasurableSet U)
  (w : U → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (hSF : RestrictedStrongFeller.HasStrongFellerNoise ρ F hF)
  (d : RankOneSpectralData
    (RestrictedStrongFeller.rawTransferOperator ρ F hF U hU w hw hw0 R hR hwR hSF)
    (1 : U →ᵇ ℝ))

/-- On the compact literal live-state space, raw spectral data alone supply
the finite leading measure and the actual quasi-ergodic density product. -/
theorem exists_quasiErgodic_of_rawRankOne :
    ∃ μ : Measure U, IsFiniteMeasure μ ∧
      (∀ f : U →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) ∧
      (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR).IsQuasiErgodic
        (LeanShared.eigenvectorMeasure μ d.eigenvector) := by
  have hP (f : U →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : U) :
      0 ≤ RestrictedStrongFeller.rawTransferOperator ρ F hF U hU w hw hw0 R hR hwR hSF f x := by
    change 0 ≤ R * RestrictedStrongFeller.transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF f x
    exact mul_nonneg hR.le
      (RestrictedStrongFeller.transferOperator_nonneg ρ F hF U hU w hw hw0 R hR hwR hSF f hf x)
  let μ := d.eigenmeasure hP
  have hm (f : U →ᵇ ℝ) : d.mean f = ∫ y, f y ∂μ := d.eigenmeasure_represents hP f
  refine ⟨μ, inferInstance, hm, ?_⟩
  exact raw_eigenvectorMeasure_isQuasiErgodic ρ F hF U hU w hw hw0 R hR hwR hSF d μ hm

end ConditionedStochasticStabilityHyperbolic.RestrictedQuasiErgodic
