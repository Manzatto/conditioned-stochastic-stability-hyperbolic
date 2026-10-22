module
public import LeanShared.Dynamics.FiniteObservationIntegral

/-! An exponential upper bound on the actual observation fibers yields
the reverse entropy-energy inequality. Zero-mass fibers are discarded only
on their proved null union, not by a positivity assumption. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.FiniteObservationEntropy
variable {X I : Type*} [MeasurableSpace X] [Fintype I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

theorem information_lower_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → I) (measurable : Measurable g) (f : X → ℝ) (integrable : Integrable f μ)
    (A : ℝ) (upper : ∀ x, μ.real (g ⁻¹' {g x}) ≤ Real.exp (f x - A)) :
    A ≤ entropy μ g + ∫ x, f x ∂μ := by
  have avoids (i : I) : ∀ᵐ x ∂μ, μ.real (g ⁻¹' {i}) = 0 → g x ≠ i := by
    by_cases zero : μ.real (g ⁻¹' {i}) = 0
    · have null : μ (g ⁻¹' {i}) = 0 := (measureReal_eq_zero_iff (μ := μ) (s := g ⁻¹' {i})).mp zero
      have neq : ∀ᵐ x ∂μ, g x ≠ i := by
        rw [ae_iff]
        simpa only [not_not, Set.preimage, mem_singleton_iff] using null
      exact neq.mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => (zero h).elim)
  have all : ∀ᵐ x ∂μ, ∀ i : I, μ.real (g ⁻¹' {i}) = 0 → g x ≠ i :=
    ae_all_iff.mpr avoids
  have pointwise : ∀ᵐ x ∂μ, A ≤ -Real.log (μ.real (g ⁻¹' {g x})) + f x := by
    filter_upwards [all] with x hx
    have nonzero : μ.real (g ⁻¹' {g x}) ≠ 0 := fun h => hx (g x) h rfl
    have positive : 0 < μ.real (g ⁻¹' {g x}) := lt_of_le_of_ne measureReal_nonneg (Ne.symm nonzero)
    have logarithm := Real.log_le_log positive (upper x)
    rw [Real.log_exp] at logarithm
    linarith
  let info : I → ℝ := fun i => -Real.log (μ.real (g ⁻¹' {i}))
  have infoFinite : Integrable info (μ.map g) := Integrable.of_finite
  have intInfo : Integrable (fun x => info (g x)) μ :=
    Integrable.comp_measurable (f := g) (g := info) infoFinite measurable
  have infoIntegral : (∫ x, info (g x) ∂μ) = entropy μ g := by
    rw [integral_observation μ g measurable info]
    simp only [info, mul_neg, Finset.sum_neg_distrib, entropy]
  have bound := integral_mono_ae (integrable_const A) (intInfo.add integrable) pointwise
  change (∫ x, A ∂μ) ≤ ∫ x, info (g x) + f x ∂μ at bound
  rw [integral_add intInfo integrable, infoIntegral] at bound
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] using bound

end LeanShared.FiniteObservationEntropy
