module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ConditionedAverages
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The left eigenmeasure follows from the rank-one power gap

The normalized power limit is unchanged by multiplying by one additional
transfer step. Its rank-one functional is therefore a left eigenfunctional.
When bounded continuous functions determine finite Borel measures, the
representing measure is consequently a genuine kernel eigenmeasure. The
measurable integral equation is proved from that measure equality.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction ENNReal

namespace ConditionedStochasticStabilityHyperbolic

namespace RankOneSpectralData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one)

/-- The limiting rank-one projection absorbs one further normalized step. -/
theorem projection_mul_normalizedOperator :
    d.projection * d.normalizedOperator = d.projection := by
  have hl := d.tendsto_powers.mul (tendsto_const_nhds (x := d.normalizedOperator))
  have hr := d.tendsto_powers.comp (tendsto_add_atTop_nat 1)
  have he : (fun n : ℕ => d.normalizedOperator ^ n * d.normalizedOperator) =
      (fun n : ℕ => d.normalizedOperator ^ (n + 1)) := by
    funext n
    exact (pow_succ _ _).symm
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

/-- Left invariance of the normalized leading eigenfunctional is derived data. -/
theorem mean_normalizedOperator (f : E) : d.mean (d.normalizedOperator f) = d.mean f := by
  have he := congrArg (fun A : E →L[ℝ] E => d.mean (A f))
    d.projection_mul_normalizedOperator
  simpa only [mul_apply_eq_comp, projection, ContinuousLinearMap.smulRight_apply,
    map_smul, d.mean_eigenvector, smul_eq_mul, mul_one] using he

/-- The eigenfunctional equation at the original positive leading rate. -/
theorem left_eigenfunctional (f : E) : d.mean (P f) = d.rate * d.mean f := by
  have he := d.mean_normalizedOperator f
  simp only [normalizedOperator, smul_apply, map_smul, smul_eq_mul] at he
  calc
    d.mean (P f) = d.rate * (d.rate⁻¹ * d.mean (P f)) := by
      rw [← mul_assoc, mul_inv_cancel₀ d.rate_pos.ne', one_mul]
    _ = d.rate * d.mean f := by rw [he]

end RankOneSpectralData

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [HasOuterApproxClosed X]
  {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
  (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
  (K : Kernel X X) [IsFiniteKernel K]
  (hP : ∀ (f : X →ᵇ ℝ) (x : X), (P f) x = ∫ y, f y ∂K x)
  (μ : Measure X) [IsFiniteMeasure μ]
  (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)

include hP hmean

/-- The continuous spectral functional determines an actual left kernel eigenmeasure.
`HasOuterApproxClosed` is automatic for metric spaces. -/
theorem rankOne_left_eigenmeasure : K ∘ₘ μ = ENNReal.ofReal d.rate • μ := by
  have : IsFiniteMeasure (ENNReal.ofReal d.rate • μ) :=
    μ.smul_finite ENNReal.ofReal_ne_top
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hint : (∫ y, f y ∂(K ∘ₘ μ)) = ∫ x, ∫ y, f y ∂K x ∂μ := by
    rw [Measure.comp_eq_comp_const_apply]
    exact Kernel.integral_comp (f.integrable _)
  rw [hint, integral_smul_measure, ENNReal.toReal_ofReal d.rate_pos.le, smul_eq_mul]
  have he := d.left_eigenfunctional f
  rw [hmean (P f), hmean f] at he
  simpa only [hP] using he

/-- The left eigenmeasure equation for any integrable observable, obtained
without assuming a separate measurable eigenmeasure identity. -/
theorem rankOne_integral_kernel (f : X → ℝ) (hf : Integrable f μ) :
    (∫ x, ∫ y, f y ∂K x ∂μ) = d.rate * ∫ y, f y ∂μ := by
  have hleft := rankOne_left_eigenmeasure d K hP μ hmean
  have hfi : Integrable f (K ∘ₘ μ) := by
    rw [hleft]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  have hint : (∫ y, f y ∂(K ∘ₘ μ)) = ∫ x, ∫ y, f y ∂K x ∂μ := by
    rw [Measure.comp_eq_comp_const_apply] at hfi ⊢
    exact Kernel.integral_comp (a := ()) hfi
  rw [← hint, hleft, integral_smul_measure, ENNReal.toReal_ofReal d.rate_pos.le,
    smul_eq_mul]

end ConditionedStochasticStabilityHyperbolic
