module

public import LeanShared.Probability.RandomMapKernel
public import LeanShared.Probability.WeightedConditioning
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Positive noisy transitions from admissible controls

An admissible control whose endpoint lies in an open target produces positive
actual transition mass when the noise law charges every nonempty open set.
Killing is allowed on exit from an open live region. Departure weights need
only be positive at the particular departure state; no global positivity or
irreducibility is asserted.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LeanShared.NoiseAccessibility

open RandomMapKernel WeightedConditioning

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [TopologicalSpace X] [TopologicalSpace Ω] [BorelSpace X]

/-- Explicit full-support formulation: the admissible control is a witness
for a nonempty open preimage in noise space. -/
theorem transition_pos_of_control (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (hρ : ∀ A : Set Ω, IsOpen A → A.Nonempty → 0 < ρ A)
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (x : X) (V : Set X) (hV : IsOpen V) (ω : Ω) (hω : F (x, ω) ∈ V) :
    0 < transition ρ F hF x V := by
  rw [transition_apply, Measure.map_apply
    (show Measurable (fun ω => F (x, ω)) from hF.comp measurable_prodMk_left)
    hV.measurableSet]
  exact hρ _ (hV.preimage (hFc.comp (continuous_const.prodMk continuous_id))) ⟨ω, hω⟩

/-- Typeclass full-support formulation. -/
theorem transition_pos (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (x : X) (V : Set X) (hV : IsOpen V) (ω : Ω) (hω : F (x, ω) ∈ V) :
    0 < transition ρ F hF x V :=
  transition_pos_of_control ρ (fun _ hA hne => hA.measure_pos ρ hne)
    F hF hFc x V hV ω hω

/-- The endpoint must lie in both the open live region and the open target. -/
theorem killed_pos (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (x : X) (ω : Ω) (hωU : F (x, ω) ∈ U) (hωV : F (x, ω) ∈ V) :
    0 < killed ρ F hF U hU.measurableSet x V := by
  change 0 < ((transition ρ F hF x).restrict U) V
  rw [Measure.restrict_apply hV.measurableSet]
  exact transition_pos ρ F hF hFc x (V ∩ U) (hV.inter hU) ω ⟨hωV, hωU⟩

/-- Positive normalization and a positive departure weight preserve
the positive mass produced by the controlled endpoint. -/
theorem normalized_killed_pos (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (x : X) (hx : 0 < w x) (ω : Ω)
    (hωU : F (x, ω) ∈ U) (hωV : F (x, ω) ∈ V) :
    0 < normalizedKernel (killed ρ F hF U hU.measurableSet) w R hw x V := by
  change 0 < (ENNReal.ofReal (w x / R) • killed ρ F hF U hU.measurableSet x) V
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (div_pos hx hR)).ne'
    (killed_pos ρ F hF hFc U V hU hV x ω hωU hωV).ne'

/-- A nonnegative continuous observable positive at the controlled live
endpoint has a strictly positive killed integral. Integrability is explicit. -/
theorem integral_killed_pos (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (U : Set X) (hU : IsOpen U) (g : X → ℝ) (hgc : Continuous g)
    (hg0 : ∀ y, 0 ≤ g y) (x : X)
    (hgi : Integrable g (killed ρ F hF U hU.measurableSet x))
    (ω : Ω) (hωU : F (x, ω) ∈ U) (hωg : 0 < g (F (x, ω))) :
    0 < ∫ y, g y ∂killed ρ F hF U hU.measurableSet x := by
  apply (integral_pos_iff_support_of_nonneg hg0 hgi).mpr
  have hp := killed_pos ρ F hF hFc U {y | 0 < g y} hU
    (isOpen_lt continuous_const hgc) x ω hωU hωg
  exact hp.trans_le (measure_mono (fun y hy => ne_of_gt hy))

/-- Feasible departure states for a fixed finite control word. Every
controlled arrival remains live, and every departure has positive weight. -/
def controlDomain (F : X × Ω → X) (U : Set X) (w : X → ℝ) (V : Set X) :
    List Ω → Set X
  | [] => V
  | ω :: controls => {x | 0 < w x} ∩
      (fun x => F (x, ω)) ⁻¹' (U ∩ controlDomain F U w V controls)

omit [MeasurableSpace X] [MeasurableSpace Ω] [BorelSpace X] in
/-- An open positive-weight basin makes each finite feasible domain open. -/
theorem isOpen_controlDomain (F : X × Ω → X) (hFc : Continuous F)
    (U : Set X) (hU : IsOpen U) (w : X → ℝ) (hwposOpen : IsOpen {x | 0 < w x})
    (V : Set X) (hV : IsOpen V) (controls : List Ω) :
    IsOpen (controlDomain F U w V controls) := by
  induction controls with
  | nil => exact hV
  | cons ω controls ih =>
      exact hwposOpen.inter
        ((hU.inter ih).preimage (hFc.comp (continuous_id.prodMk continuous_const)))

/-- A feasible fixed finite control word has positive actual killed endpoint
mass. An open positive-weight basin ensures nearby departures retain
positive weight. This is a finite accessibility statement, not irreducibility. -/
theorem normalized_killed_pow_pos (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (U : Set X) (hU : IsOpen U) (w : X → ℝ) (hw : Measurable w)
    (hwposOpen : IsOpen {x | 0 < w x}) (R : ℝ) (hR : 0 < R)
    (V : Set X) (hV : IsOpen V) (controls : List Ω)
    (x : X) (hx : x ∈ controlDomain F U w V controls) :
    0 < (normalizedKernel (killed ρ F hF U hU.measurableSet) w R hw ^
      controls.length) x V := by
  let K := normalizedKernel (killed ρ F hF U hU.measurableSet) w R hw
  change 0 < (K ^ controls.length) x V
  induction controls generalizing x with
  | nil =>
      change 0 < (Measure.dirac x) V
      rw [Measure.dirac_apply' _ hV.measurableSet]
      rw [indicator_of_mem (show x ∈ V from hx)]
      exact zero_lt_one
  | cons ω controls ih =>
      change 0 < (K ^ (controls.length + 1)) x V
      rw [pow_succ]
      change 0 < ((K ^ controls.length) ∘ₖ K) x V
      rw [Kernel.comp_apply' _ _ _ hV.measurableSet]
      apply (lintegral_pos_iff_support ((K ^ controls.length).measurable_coe hV.measurableSet)).mpr
      have hp : 0 < K x (controlDomain F U w V controls) :=
        normalized_killed_pos ρ F hF hFc U (controlDomain F U w V controls) hU
          (isOpen_controlDomain F hFc U hU w hwposOpen V hV controls)
          w hw R hR x hx.1 ω hx.2.1 hx.2.2
      exact hp.trans_le (measure_mono (fun y hy => (ih y hy).ne'))

end LeanShared.NoiseAccessibility
