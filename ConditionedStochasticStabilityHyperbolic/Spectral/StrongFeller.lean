module

public import ConditionedStochasticStabilityHyperbolic.Spectral.MeasurableObservables

/-!
# Strong-Feller kernels supply bounded measurable observation operators

Only continuity of the kernel integral of each bounded measurable real
function is assumed. Uniform bounds, integrability, linearity and boundedness
of `f ↦ K(h*f)` are proved from the canonical killed kernel's mass bound.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The usual strong-Feller property for the real bounded-measurable kernel
integral. No regularity of the density or operator-norm continuity is assumed. -/
def HasStrongFellerKernel (C : AbsorbingMarkovChains.CanonicalChain X) : Prop :=
  ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖f y‖ ≤ B) →
    Continuous (fun x => ∫ y, f y ∂C.killedTransition x)

namespace StrongFeller

variable (C : AbsorbingMarkovChains.CanonicalChain X)

local instance killedKernelFinite : IsFiniteKernel C.killedTransition := by
  change IsFiniteKernel C.toKilledKernel.kernel
  infer_instance

omit [TopologicalSpace X] in
/-- Every canonical killed transition has real mass at most one. -/
theorem killedTransition_real_mass_le_one (x : X) :
    (C.killedTransition x).real univ ≤ 1 := by
  change (C.killedTransition x univ).toReal ≤ (1 : ENNReal).toReal
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
    (C.killedTransition_mass_le_one x)

variable {h : X → ℝ} (hh : Measurable h) {B : ℝ}
  (hB : 0 ≤ B) (hbound : ∀ y, ‖h y‖ ≤ B)
  [OpensMeasurableSpace X]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
include hB hbound in
theorem product_bound (f : X →ᵇ ℝ) (y : X) : ‖h y * f y‖ ≤ B * ‖f‖ := by
  rw [norm_mul]
  exact mul_le_mul (hbound y) (f.norm_coe_le_norm y) (norm_nonneg _) hB

include hh hB hbound in
theorem product_integrable (f : X →ᵇ ℝ) (x : X) :
    Integrable (fun y => h y * f y) (C.killedTransition x) := by
  apply Integrable.of_bound (hh.mul f.continuous.measurable).aestronglyMeasurable (B * ‖f‖)
  exact ae_of_all _ (product_bound hB hbound f)

omit [OpensMeasurableSpace X] in
include hB hbound in
theorem integral_product_bound (f : X →ᵇ ℝ) (x : X) :
    ‖∫ y, h y * f y ∂C.killedTransition x‖ ≤ B * ‖f‖ := by
  calc
    ‖∫ y, h y * f y ∂C.killedTransition x‖ ≤
        (B * ‖f‖) * (C.killedTransition x).real univ :=
      norm_integral_le_of_norm_le_const (ae_of_all _ (product_bound hB hbound f))
    _ ≤ B * ‖f‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (killedTransition_real_mass_le_one C x) (mul_nonneg hB (norm_nonneg f))

variable (hSF : HasStrongFellerKernel C)

/-- The continuous function obtained after integrating one measurable product. -/
def observationFunction (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ∫ y, h y * f y ∂C.killedTransition x)
    (hSF _ (hh.mul f.continuous.measurable)
      ⟨B * ‖f‖, mul_nonneg hB (norm_nonneg f), product_bound hB hbound f⟩)
    (B * ‖f‖) (integral_product_bound C hB hbound f)

theorem observationFunction_apply (f : X →ᵇ ℝ) (x : X) :
    observationFunction C hh hB hbound hSF f x =
      ∫ y, h y * f y ∂C.killedTransition x := rfl

/-- Linearity of the smoothing map follows from integrability of its products. -/
def observationLinearMap : (X →ᵇ ℝ) →ₗ[ℝ] (X →ᵇ ℝ) where
  toFun := observationFunction C hh hB hbound hSF
  map_add' f g := by
    ext x
    change (∫ y, h y * (f + g) y ∂C.killedTransition x) =
      (∫ y, h y * f y ∂C.killedTransition x) + ∫ y, h y * g y ∂C.killedTransition x
    simp only [BoundedContinuousFunction.add_apply, mul_add]
    exact integral_add (product_integrable C hh hB hbound f x)
      (product_integrable C hh hB hbound g x)
  map_smul' a f := by
    ext x
    change (∫ y, h y * (a • f) y ∂C.killedTransition x) =
      a * ∫ y, h y * f y ∂C.killedTransition x
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul]
    have heq : (fun y => h y * (a * f y)) = (fun y => a * (h y * f y)) := by
      funext y
      ring
    rw [heq]
    exact integral_const_mul a _

/-- The observation smoothing map is bounded by the observable's uniform bound. -/
theorem observationLinearMap_bound (f : X →ᵇ ℝ) :
    ‖observationLinearMap C hh hB hbound hSF f‖ ≤ B * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hB (norm_nonneg f))).2
  exact integral_product_bound C hB hbound f

/-- Strong Feller continuity plus the sub-Markov mass bound constructs the
actual bounded linear map required by the measurable-average theorem. -/
def observationOperator : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ) :=
  (observationLinearMap C hh hB hbound hSF).mkContinuous B
    (observationLinearMap_bound C hh hB hbound hSF)

theorem observationOperator_apply (f : X →ᵇ ℝ) (x : X) :
    observationOperator C hh hB hbound hSF f x =
      ∫ y, h y * f y ∂C.killedTransition x := rfl

/-- Every bounded measurable observable supplies its smoothing interface from the standard
strong-Feller property alone. -/
def smoothedObservable : SmoothedObservable C h where
  measurable := hh
  bound := B
  bound_nonneg := hB
  norm_le := hbound
  operator := observationOperator C hh hB hbound hSF
  represents := observationOperator_apply C hh hB hbound hSF

/-- The smoothing operator norm is controlled by the observable bound. -/
theorem norm_observationOperator_le :
    ‖observationOperator C hh hB hbound hSF‖ ≤ B := by
  apply LinearMap.mkContinuous_norm_le _ hB

end StrongFeller

section Consequences

variable [OpensMeasurableSpace X] (C : AbsorbingMarkovChains.CanonicalChain X)
  (hSF : HasStrongFellerKernel C)

include hSF in
/-- A bound with unspecified sign can always be replaced by a nonnegative one. -/
theorem exists_smoothedObservable (h : X → ℝ) (hh : Measurable h)
    (hb : ∃ B : ℝ, ∀ y, ‖h y‖ ≤ B) : Nonempty (SmoothedObservable C h) := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨StrongFeller.smoothedObservable C hh (le_max_right B 0)
    (fun y => (hB y).trans (le_max_left B 0)) hSF⟩

/-- The unweighted continuous transfer operator is also constructed from
the standard strong-Feller property. -/
def strongFellerTransferOperator : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ) :=
  StrongFeller.observationOperator C (h := fun _ => (1 : ℝ)) measurable_const
    zero_le_one (fun _ => by simp) hSF

theorem strongFellerTransferOperator_represents (f : X →ᵇ ℝ) (x : X) :
    strongFellerTransferOperator C hSF f x = ∫ y, f y ∂C.killedTransition x := by
  change (∫ y, (1 : ℝ) * f y ∂C.killedTransition x) = _
  simp only [one_mul]

theorem norm_strongFellerTransferOperator_le_one :
    ‖strongFellerTransferOperator C hSF‖ ≤ 1 :=
  StrongFeller.norm_observationOperator_le C measurable_const zero_le_one
    (fun _ => by simp) hSF

end Consequences

end ConditionedStochasticStabilityHyperbolic
