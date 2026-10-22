module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Spectral.QuasiErgodic

/-!
# Quasi-ergodicity for the literal weighted noisy chain

Jointly measurable noise maps, standard unweighted strong Feller regularity,
and a continuous bounded nonnegative weight construct both the `Option U`
chain and its continuous transfer operator. Its rank-one spectral gap and
the finite measure representing its functional remain explicit inputs. Nonnegativity of the eigenfunction follows from positivity of the transfer
and its normalized power limit; smoothing and the measurable eigenmeasure
identity are consequently discharged by the checked adapters.

No positivity on a basic set or support inclusion is proved here. Uniqueness
retains the positive-basin/support qualification.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.RestrictedQuasiErgodic

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
  (F : X × Ω → X) (hF : Measurable F) (U : Set X) (hU : MeasurableSet U)
  (w : U → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (hSF : RestrictedStrongFeller.HasStrongFellerNoise ρ F hF)

variable (d : RankOneSpectralData
  (RestrictedStrongFeller.transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF)
  (1 : U →ᵇ ℝ))

/-- The genuine positive transfer fixes the sign of the normalized leading
eigenfunction; this is a consequence of the given spectral gap. -/
theorem eigenvector_nonneg (x : U) : 0 ≤ d.eigenvector x := by
  have hQ (f : U →ᵇ ℝ) (hf : ∀ y, 0 ≤ f y) (y : U) :
      0 ≤ d.normalizedOperator f y := by
    rw [RankOneSpectralData.normalizedOperator, smul_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr d.rate_pos.le)
      (RestrictedStrongFeller.transferOperator_nonneg ρ F hF U hU w hw hw0 R hR hwR hSF f hf y)
  have hn (n : ℕ) (y : U) : 0 ≤ ((d.normalizedOperator ^ n) 1) y := by
    induction n generalizing y with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp]
        exact hQ _ ih y
  let V : ((U →ᵇ ℝ) →L[ℝ] (U →ᵇ ℝ)) →L[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (ContinuousLinearMap.apply ℝ (U →ᵇ ℝ) 1)
  have hlim := V.continuous.continuousAt.tendsto.comp d.tendsto_powers
  have hV : V d.projection = d.mean 1 * d.eigenvector x := by
    simp only [V, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      RankOneSpectralData.projection, ContinuousLinearMap.smulRight_apply,
      BoundedContinuousFunction.evalCLM_apply, BoundedContinuousFunction.smul_apply,
      smul_eq_mul]
  change Tendsto (fun n => ((d.normalizedOperator ^ n) 1) x) atTop (𝓝 (V d.projection)) at hlim
  rw [hV] at hlim
  have hpos : 0 ≤ d.mean 1 * d.eigenvector x :=
    ge_of_tendsto hlim (Eventually.of_forall fun n => hn n x)
  exact (mul_nonneg_iff_of_pos_left d.mean_one_pos).mp hpos

variable (μ : Measure U) [IsFiniteMeasure μ]
  (hmean : ∀ f : U →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)

include hmean in
/-- Actual bounded-measurable quasi-ergodicity of the literal weighted noisy
process. The remaining substantive input is the displayed rank-one spectral data. -/
theorem eigenvectorMeasure_isQuasiErgodic :
    (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR).IsQuasiErgodic
      (LeanShared.eigenvectorMeasure μ d.eigenvector) := by
  exact QuasiErgodic.eigenvectorMeasure_isQuasiErgodic_of_strongFeller
    (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR)
    (RestrictedStrongFeller.transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF)
    (RestrictedStrongFeller.transferOperator_represents ρ F hF U hU w hw hw0 R hR hwR hSF)
    d μ hmean (eigenvector_nonneg ρ F hF U hU w hw hw0 R hR hwR hSF d)
    (RestrictedStrongFeller.hasStrongFeller_chain ρ F hF U hU w hw hw0 R hR hwR hSF)

include hmean in
/-- The concrete noisy process has the usual qualified uniqueness: a
competing QEM whose support meets the positive eigenfunction basin equals `g μ`. -/
theorem eq_eigenvectorMeasure_of_support (ν : Measure U)
    (hq : (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR).IsQuasiErgodic ν)
    (p : U) (hp : p ∈ ν.support) (hgp : 0 < d.eigenvector p) :
    ν = LeanShared.eigenvectorMeasure μ d.eigenvector := by
  exact QuasiErgodic.eq_eigenvectorMeasure_of_support
    (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR)
    (RestrictedStrongFeller.transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF)
    (RestrictedStrongFeller.transferOperator_represents ρ F hF U hU w hw hw0 R hR hwR hSF)
    d μ hmean (eigenvector_nonneg ρ F hF U hU w hw hw0 R hR hwR hSF d) ν hq p hp hgp

include hmean in
/-- Positivity on a nonempty basic set suffices for uniqueness among QEMs
whose support contains that set; that geometric positivity remains a hypothesis. -/
theorem eq_eigenvectorMeasure_of_basicSet_support
    (Λ : Set U) (hΛ : Λ.Nonempty) (hgΛ : ∀ x ∈ Λ, 0 < d.eigenvector x)
    (ν : Measure U)
    (hq : (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR).IsQuasiErgodic ν)
    (hsupp : Λ ⊆ ν.support) :
    ν = LeanShared.eigenvectorMeasure μ d.eigenvector := by
  obtain ⟨p, hp⟩ := hΛ
  exact eq_eigenvectorMeasure_of_support ρ F hF U hU w hw hw0 R hR hwR hSF
    d μ hmean ν hq p (hsupp hp) (hgΛ p hp)

end ConditionedStochasticStabilityHyperbolic.RestrictedQuasiErgodic
