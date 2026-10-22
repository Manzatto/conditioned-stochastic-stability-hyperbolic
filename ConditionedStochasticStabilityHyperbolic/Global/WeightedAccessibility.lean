module

public import LeanShared.Probability.NoiseAccessibility
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise

/-!
# Actual weighted accessibility and backward eigenfunction positivity

Continuous full-support noise turns explicitly feasible controls into positive
mass for the actual weighted killed kernel and canonical path law. Finite
words require an open positive-weight basin for robust probability access.
Backward positivity of a continuous nonnegative eigenfunction only requires
positive weights at the controlled departures. No heteroclinic relation is
converted into a controlled path here, and positivity on a basic set remains
an input when that is the terminal set.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace ConditionedStochasticStabilityHyperbolic.Global.WeightedAccessibility

open AbsorbingMarkovChains LeanShared.RandomMapKernel LeanShared.WeightedConditioning
open LeanShared.NoiseAccessibility

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [TopologicalSpace X] [TopologicalSpace Ω] [BorelSpace X]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
  (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
  (U : Set X) (hU : IsOpen U) (w : X → ℝ) (hw : Measurable w)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)

include hFc

/-- Positive actual killed one-step transition, with the literal normalized
departure weight of the paper's chain. -/
theorem killedTransition_pos (V : Set X) (hV : IsOpen V)
    (x : X) (hx : 0 < w x) (ω : Ω)
    (hωU : F (x, ω) ∈ U) (hωV : F (x, ω) ∈ V) :
    0 < (NoiseKernel.chain ρ F hF U hU.measurableSet w hw R hR hwR).killedTransition x V := by
  rw [NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  exact normalized_killed_pos ρ F hF hFc U V hU hV w hw R hR x hx ω hωU hωV

/-- The feasible word gives positive probability for the genuine canonical
path to be alive in the target at its terminal time. -/
theorem pathMeasure_endpoint_pos (hwposOpen : IsOpen {x | 0 < w x}) (V : Set X) (hV : IsOpen V)
    (controls : List Ω) (x : X) (hx : x ∈ controlDomain F U w V controls) :
    0 < (NoiseKernel.chain ρ F hF U hU.measurableSet w hw R hR hwR).pathMeasure x
      {path | path controls.length ∈ Option.some '' V} := by
  rw [← CanonicalChain.killedTransition_pow_apply _ x controls.length V hV.measurableSet,
    NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  exact normalized_killed_pow_pos ρ F hF hFc U hU w hw hwposOpen R hR V hV controls x hx

/-- Such a finite feasible word also guarantees positive actual survival. -/
theorem pathMeasure_survival_pos (hwposOpen : IsOpen {x | 0 < w x}) (V : Set X) (hV : IsOpen V)
    (controls : List Ω) (x : X) (hx : x ∈ controlDomain F U w V controls) :
    0 < (NoiseKernel.chain ρ F hF U hU.measurableSet w hw R hR hwR).pathMeasure x
      (CanonicalChain.survival controls.length) := by
  rw [CanonicalChain.pathMeasure_survival]
  have hp := pathMeasure_endpoint_pos ρ F hF hFc U hU w hw R hR hwR hwposOpen V hV controls x hx
  rw [← CanonicalChain.killedTransition_pow_apply _ x controls.length V hV.measurableSet] at hp
  exact hp.trans_le (measure_mono (subset_univ V))

/-- Full positive probability under the actual survival-conditioned path law. -/
theorem conditionedMeasure_endpoint_pos (hwposOpen : IsOpen {x | 0 < w x}) (V : Set X) (hV : IsOpen V)
    (controls : List Ω) (x : X) (hx : x ∈ controlDomain F U w V controls) :
    0 < (NoiseKernel.chain ρ F hF U hU.measurableSet w hw R hR hwR).conditionedMeasure x
      controls.length {path | path controls.length ∈ Option.some '' V} := by
  rw [CanonicalChain.conditionedMeasure_endpoint _ x controls.length V hV.measurableSet]
  have hp := pathMeasure_endpoint_pos ρ F hF hFc U hU w hw R hR hwR hwposOpen V hV controls x hx
  rw [← CanonicalChain.killedTransition_pow_apply _ x controls.length V hV.measurableSet] at hp
  have hfinite := lt_of_le_of_lt
    (CanonicalChain.killedTransition_pow_mass_le_one
      (NoiseKernel.chain ρ F hF U hU.measurableSet w hw R hR hwR) x controls.length)
    ENNReal.one_lt_top
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hfinite.ne) hp.ne'

/-- Transfer-eigenfunction positivity propagates backward through one
admissible live control. The leading eigenvalue is strictly positive. -/
theorem eigenfunction_pos_of_control (g : X → ℝ) (hgc : Continuous g)
    (hg0 : ∀ y, 0 ≤ g y) (l : ℝ) (hl : 0 < l)
    (heigen : ∀ x, (∫ y, g y
      ∂(NoiseKernel.chain ρ F hF U hU.measurableSet w hw R hR hwR).killedTransition x) = l * g x)
    (x : X) (hgi : Integrable g (killed ρ F hF U hU.measurableSet x))
    (hx : 0 < w x) (ω : Ω) (hωU : F (x, ω) ∈ U) (hωg : 0 < g (F (x, ω))) :
    0 < g x := by
  have hp := integral_killed_pos ρ F hF hFc U hU g hgc hg0 x hgi ω hωU hωg
  have hi : 0 < ∫ y, g y
      ∂(NoiseKernel.chain ρ F hF U hU.measurableSet w hw R hR hwR).killedTransition x := by
    rw [NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
    change 0 < ∫ y, g y ∂(ENNReal.ofReal (w x / R) • killed ρ F hF U hU.measurableSet x)
    rw [integral_smul_measure, ENNReal.toReal_ofReal (div_pos hx hR).le, smul_eq_mul]
    exact mul_pos (div_pos hx hR) hp
  rw [heigen x] at hi
  exact pos_of_mul_pos_right hi hl.le

/-- Backward positivity along a fixed finite feasible word. Continuity of
the departure weight is unnecessary: each controlled departure is explicitly
positive. Only the eigenfunction's positive terminal basin is used. -/
theorem eigenfunction_pos_of_controlWord (g : X → ℝ) (hgc : Continuous g)
    (hg0 : ∀ y, 0 ≤ g y) (l : ℝ) (hl : 0 < l)
    (heigen : ∀ x, (∫ y, g y
      ∂(NoiseKernel.chain ρ F hF U hU.measurableSet w hw R hR hwR).killedTransition x) = l * g x)
    (hgi : ∀ x, Integrable g (killed ρ F hF U hU.measurableSet x))
    (controls : List Ω) (x : X)
    (hx : x ∈ controlDomain F U w {y | 0 < g y} controls) : 0 < g x := by
  induction controls generalizing x with
  | nil => exact hx
  | cons ω controls ih =>
      exact eigenfunction_pos_of_control ρ F hF hFc U hU w hw R hR hwR g hgc hg0
        l hl heigen x (hgi x) hx.1 ω hx.2.1 (ih _ hx.2.2)

/-- The same one-step positivity for the literal live-state subtype. The
departure weight is defined only on `U`, as in the actual killed process. -/
theorem restricted_killedTransition_pos (v : U → ℝ) (hv : Measurable v)
    (hvR : ∀ x, v x ≤ R) (V : Set X) (hV : IsOpen V)
    (x : U) (hx : 0 < v x) (ω : Ω)
    (hωU : F (x.val, ω) ∈ U) (hωV : F (x.val, ω) ∈ V) :
    0 < (RestrictedNoise.chain ρ F hF U hU.measurableSet v hv R hR hvR).killedTransition x
      (Subtype.val ⁻¹' V) := by
  rw [RestrictedNoise.killedTransition]
  change 0 < (ENNReal.ofReal (v x / R) •
    RestrictedNoise.liveKernel ρ F hF U hU.measurableSet x) (Subtype.val ⁻¹' V)
  rw [Measure.smul_apply, smul_eq_mul, RestrictedNoise.liveKernel,
    LeanShared.SubtypeKernel.restrict_apply_set _ U hU.measurableSet x _
      (hV.measurableSet.preimage measurable_subtype_coe)]
  have himage : Subtype.val '' (Subtype.val ⁻¹' V : Set U) = V ∩ U := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.property⟩
    · rintro ⟨hyV, hyU⟩
      exact ⟨⟨y, hyU⟩, hyV, rfl⟩
  rw [himage]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (div_pos hx hR)).ne'
    (transition_pos ρ F hF hFc x.val (V ∩ U) (hV.inter hU) ω ⟨hωV, hωU⟩).ne'

/-- Backward positivity also works for an eigenfunction defined and
continuous only on the actual open live region. -/
theorem restricted_eigenfunction_pos_of_control (v : U → ℝ) (hv : Measurable v)
    (hvR : ∀ x, v x ≤ R) (g : U → ℝ) (hgc : Continuous g)
    (hg0 : ∀ y, 0 ≤ g y) (l : ℝ) (hl : 0 < l)
    (heigen : ∀ x, (∫ y, g y
      ∂(RestrictedNoise.chain ρ F hF U hU.measurableSet v hv R hR hvR).killedTransition x) = l * g x)
    (x : U) (hgi : Integrable g
      ((RestrictedNoise.chain ρ F hF U hU.measurableSet v hv R hR hvR).killedTransition x))
    (hx : 0 < v x) (ω : Ω) (hωU : F (x.val, ω) ∈ U)
    (hωg : 0 < g ⟨F (x.val, ω), hωU⟩) : 0 < g x := by
  let V : Set X := Subtype.val '' {y : U | 0 < g y}
  have hV : IsOpen V := hU.isOpenMap_subtype_val _ (isOpen_lt continuous_const hgc)
  have hp := restricted_killedTransition_pos ρ F hF hFc U hU R hR
    v hv hvR V hV x hx ω hωU ⟨⟨F (x.val, ω), hωU⟩, hωg, rfl⟩
  have hs : Subtype.val ⁻¹' V ⊆ Function.support g := by
    rintro y ⟨z, hz, hzy⟩
    have heq : z = y := Subtype.val_injective hzy
    subst z
    exact ne_of_gt hz
  have hi := (integral_pos_iff_support_of_nonneg hg0 hgi).mpr
    (hp.trans_le (measure_mono hs))
  rw [heigen x] at hi
  exact pos_of_mul_pos_right hi hl.le

/-- Feasibility of controls on the literal live subtype, requiring no
extension of its weight or eigenfunction to the ambient space. -/
def liveControlDomain (v : U → ℝ) (V : Set U) : List Ω → Set U
  | [] => V
  | ω :: controls => {x | 0 < v x ∧ ∃ h : F (x.val, ω) ∈ U,
      (⟨F (x.val, ω), h⟩ : U) ∈ liveControlDomain v V controls}

/-- Finite backward positivity for a live-subtype eigenfunction. -/
theorem restricted_eigenfunction_pos_of_controlWord (v : U → ℝ) (hv : Measurable v)
    (hvR : ∀ x, v x ≤ R) (g : U → ℝ) (hgc : Continuous g)
    (hg0 : ∀ y, 0 ≤ g y) (l : ℝ) (hl : 0 < l)
    (heigen : ∀ x, (∫ y, g y
      ∂(RestrictedNoise.chain ρ F hF U hU.measurableSet v hv R hR hvR).killedTransition x) = l * g x)
    (hgi : ∀ x, Integrable g
      ((RestrictedNoise.chain ρ F hF U hU.measurableSet v hv R hR hvR).killedTransition x))
    (controls : List Ω) (x : U)
    (hx : x ∈ liveControlDomain F U v {y | 0 < g y} controls) : 0 < g x := by
  induction controls generalizing x with
  | nil => exact hx
  | cons ω controls ih =>
      obtain ⟨hxv, hωU, htail⟩ := hx
      exact restricted_eigenfunction_pos_of_control ρ F hF hFc U hU R hR
        v hv hvR g hgc hg0 l hl heigen x (hgi x) hxv ω hωU (ih _ htail)

end ConditionedStochasticStabilityHyperbolic.Global.WeightedAccessibility
