module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingSimplicity
public import AbsorbingMarkovChains.LeftSimplicity

/-!
# Uniqueness of the actual leading kernel eigenmeasure

The finite measure integral functional is reused from the stable-laws
development without any of its irreducibility hypotheses. The actual kernel
law and power gap imply uniqueness up to the eigenfunction normalization.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction ENNReal

namespace ConditionedStochasticStabilityHyperbolic

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
  (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
  (K : Kernel X X) [IsFiniteKernel K]
  (hP : ∀ (f : X →ᵇ ℝ) (x : X), P f x = ∫ y, f y ∂K x)
  (μ : Measure X) [IsFiniteMeasure μ]
  (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)

include hP in
/-- The measurable kernel eigenrelation gives the continuous left
eigenfunctional equation, with no absolute continuity assumption. -/
theorem integralFunctional_left_eigen (ν : Measure X) [IsFiniteMeasure ν]
    (hν : K ∘ₘ ν = ENNReal.ofReal d.rate • ν) (f : X →ᵇ ℝ) :
    AbsorbingMarkovChains.LeftSimplicity.integralFunctional ν (P f) =
      d.rate * AbsorbingMarkovChains.LeftSimplicity.integralFunctional ν f := by
  have hi : (∫ y, f y ∂(K ∘ₘ ν)) = ∫ x, ∫ y, f y ∂K x ∂ν := by
    rw [Measure.comp_eq_comp_const_apply]
    exact Kernel.integral_comp (f.integrable _)
  change (∫ x, P f x ∂ν) = d.rate * ∫ x, f x ∂ν
  simp only [hP]
  rw [← hi, hν, integral_smul_measure, ENNReal.toReal_ofReal d.rate_pos.le, smul_eq_mul]

include hP hmean in
/-- Same-rate finite left eigenmeasures are exactly scalar multiples, with
the scalar fixed by their pairing against the constructed eigenfunction. -/
theorem leading_eigenmeasure_eq_smul (hg : ∀ x, 0 ≤ d.eigenvector x)
    (ν : Measure X) [IsFiniteMeasure ν]
    (hν : K ∘ₘ ν = ENNReal.ofReal d.rate • ν) :
    ν = ENNReal.ofReal (∫ x, d.eigenvector x ∂ν) • μ := by
  let ℓ := AbsorbingMarkovChains.LeftSimplicity.integralFunctional ν
  have hℓ (f : X →ᵇ ℝ) : ℓ f = ∫ x, f x ∂ν :=
    AbsorbingMarkovChains.LeftSimplicity.integralFunctional_apply ν f
  have he := d.leading_eigenfunctional_eq ℓ (integralFunctional_left_eigen d K hP ν hν)
  have hc : 0 ≤ ℓ d.eigenvector := integral_nonneg hg
  let _ : IsFiniteMeasure (ENNReal.ofReal (∫ x, d.eigenvector x ∂ν) • μ) :=
    μ.smul_finite ENNReal.ofReal_ne_top
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hf := congrArg (fun q : (X →ᵇ ℝ) →L[ℝ] ℝ => q f) he
  change (∫ x, f x ∂ν) = _
  rw [integral_smul_measure, ← hℓ d.eigenvector, ENNReal.toReal_ofReal hc, smul_eq_mul, ← hmean f]
  simpa only [smul_apply, smul_eq_mul, hℓ f] using hf

include hP hmean in
/-- The manuscript's eigenfunction pairing normalization makes the leading
measure unique, without requiring it to be a probability. -/
theorem leading_eigenmeasure_eq_of_normalization (hg : ∀ x, 0 ≤ d.eigenvector x)
    (ν : Measure X) [IsFiniteMeasure ν]
    (hν : K ∘ₘ ν = ENNReal.ofReal d.rate • ν)
    (hnorm : (∫ x, d.eigenvector x ∂ν) = 1) : ν = μ := by
  simpa only [hnorm, ENNReal.ofReal_one, one_smul] using
    leading_eigenmeasure_eq_smul d K hP μ hmean hg ν hν

end ConditionedStochasticStabilityHyperbolic
