module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFeller

/-!
# Strong Feller regularity on the actual live-state subtype

Standard unweighted noise regularity, together with a continuous nonnegative
bounded departure weight on `U`, proves strong Feller regularity of the
canonical `Option U` chain. A measurable observable on `U` is extended by
zero, not by a continuous extension. Thus neither a smooth boundary nor a
continuous extension theorem is needed for this adapter.

The bounded continuous transfer and observation operators are constructed
from this property and the proved canonical mass bound. Smooth-noise
regularity itself remains the explicit cited-background input.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.RestrictedStrongFeller

variable {X Ω : Type*} [TopologicalSpace X] [MeasurableSpace X] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)

/-- Standard strong Feller regularity for the unweighted ambient noise kernel.
This supplies continuity of scalar integrals, without postulating any linear operator. -/
def HasStrongFellerNoise : Prop :=
  ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖f y‖ ≤ B) →
    Continuous (fun x => ∫ y, f y ∂LeanShared.RandomMapKernel.transition ρ F hF x)

variable [OpensMeasurableSpace X]
  (U : Set X) (hU : MeasurableSet U)
  (w : U → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (hSF : HasStrongFellerNoise ρ F hF)

include hw0 hSF in
/-- Killing on exit and normalizing a continuous departure weight preserve
strong Feller regularity on the literal live-state type. -/
theorem hasStrongFeller_chain :
    HasStrongFellerKernel (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR) := by
  intro f hf hb
  obtain ⟨B, hB0, hB⟩ := hb
  let g : X → ℝ := U.indicator (LeanShared.SubtypeKernel.zeroExtend U f)
  have hg : Measurable g :=
    (LeanShared.SubtypeKernel.measurable_zeroExtend U hU f hf).indicator hU
  have hgb (y : X) : ‖g y‖ ≤ B := by
    by_cases hy : y ∈ U
    · rw [show g y = LeanShared.SubtypeKernel.zeroExtend U f y from
        indicator_of_mem hy _]
      exact LeanShared.SubtypeKernel.norm_zeroExtend_le U f B hB0 hB y
    · rw [show g y = 0 from indicator_of_notMem hy _]
      simpa only [norm_zero] using hB0
  have hcont := hSF g hg ⟨B, hB0, hgb⟩
  have hnoise : Continuous (fun x : X => ∫ ω, g (F (x, ω)) ∂ρ) := by
    simpa only [LeanShared.RandomMapKernel.integral_transition ρ F hF g hg] using hcont
  have hweighted : Continuous (fun x : U => (w x / R) *
      ∫ ω, g (F (x.val, ω)) ∂ρ) :=
    (hw.div_const R).mul (hnoise.comp continuous_subtype_val)
  have he : (fun x : U =>
      ∫ y, f y ∂(RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR).killedTransition x) =
      (fun x : U => (w x / R) * ∫ ω, g (F (x.val, ω)) ∂ρ) := by
    funext x
    exact RestrictedNoise.integral_chain ρ F hF U hU w hw.measurable hw0 R hR hwR f hf x
  rw [he]
  exact hweighted

/-- The actual bounded continuous normalized annealed transfer operator. -/
def transferOperator : (U →ᵇ ℝ) →L[ℝ] (U →ᵇ ℝ) :=
  strongFellerTransferOperator (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR)
    (hasStrongFeller_chain ρ F hF U hU w hw hw0 R hR hwR hSF)

/-- The constructed operator has the manuscript's exact departure weight and exit indicator. -/
theorem transferOperator_apply (f : U →ᵇ ℝ) (x : U) :
    transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF f x =
      (w x / R) * ∫ ω, U.indicator (LeanShared.SubtypeKernel.zeroExtend U f)
        (F (x.val, ω)) ∂ρ := by
  rw [transferOperator, strongFellerTransferOperator_represents]
  exact RestrictedNoise.integral_chain ρ F hF U hU w hw.measurable hw0 R hR hwR
    f f.continuous.measurable x

/-- The operator represents the constructed canonical killed kernel. -/
theorem transferOperator_represents (f : U →ᵇ ℝ) (x : U) :
    transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF f x =
      ∫ y, f y ∂(RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR).killedTransition x :=
  strongFellerTransferOperator_represents _ _ f x

/-- Normalization gives a contraction in the supremum norm. -/
theorem norm_transferOperator_le_one :
    ‖transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF‖ ≤ 1 :=
  norm_strongFellerTransferOperator_le_one _ _

/-- Positivity of the actual transfer is inherited from its kernel representation. -/
theorem transferOperator_nonneg (f : U →ᵇ ℝ) (hf : ∀ y, 0 ≤ f y) (x : U) :
    0 ≤ transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF f x := by
  rw [transferOperator_represents]
  exact integral_nonneg hf

/-- The unnormalized operator used in the manuscript, constructed from the
canonical normalized transfer by multiplying back its fixed bound. -/
def rawTransferOperator : (U →ᵇ ℝ) →L[ℝ] (U →ᵇ ℝ) :=
  R • transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF

/-- The raw operator has the exact, unscaled weighted annealed formula. -/
theorem rawTransferOperator_apply (f : U →ᵇ ℝ) (x : U) :
    rawTransferOperator ρ F hF U hU w hw hw0 R hR hwR hSF f x =
      w x * ∫ ω, U.indicator (LeanShared.SubtypeKernel.zeroExtend U f)
        (F (x.val, ω)) ∂ρ := by
  simp only [rawTransferOperator, smul_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul, transferOperator_apply]
  rw [← mul_assoc, mul_comm R (w x / R), div_mul_cancel₀ _ hR.ne']

/-- The raw transfer's uniform operator bound is the departure-weight bound. -/
theorem norm_rawTransferOperator_le :
    ‖rawTransferOperator ρ F hF U hU w hw hw0 R hR hwR hSF‖ ≤ R := by
  calc
    ‖rawTransferOperator ρ F hF U hU w hw hw0 R hR hwR hSF‖ ≤
        ‖R‖ * ‖transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF‖ := by
      simpa only [rawTransferOperator] using ContinuousLinearMap.opNorm_smul_le R
        (transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF)
    _ ≤ R := by
      rw [Real.norm_of_nonneg hR.le]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (norm_transferOperator_le_one ρ F hF U hU w hw hw0 R hR hwR hSF) hR.le

/-- Rescaling back to the canonical operator changes no mathematical input. -/
theorem inv_smul_rawTransferOperator :
    R⁻¹ • rawTransferOperator ρ F hF U hU w hw hw0 R hR hwR hSF =
      transferOperator ρ F hF U hU w hw hw0 R hR hwR hSF := by
  rw [rawTransferOperator, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]

include hw0 hSF in
/-- All bounded measurable live observables acquire their actual smoothing operator. -/
theorem exists_smoothedObservable (h : U → ℝ) (hh : Measurable h)
    (hb : ∃ B : ℝ, ∀ y, ‖h y‖ ≤ B) :
    Nonempty (SmoothedObservable
      (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR) h) :=
  ConditionedStochasticStabilityHyperbolic.exists_smoothedObservable _
    (hasStrongFeller_chain ρ F hF U hU w hw hw0 R hR hwR hSF) h hh hb

end ConditionedStochasticStabilityHyperbolic.RestrictedStrongFeller
