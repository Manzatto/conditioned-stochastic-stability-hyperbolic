module

public import LeanShared.Dynamics.FiniteObservationIntegral
public import LeanShared.Dynamics.FiniteGibbsVariational

/-! Finite Gibbs optimization bounds the actual energy integral and
actual entropy of every measurable finite observation. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.FiniteObservationEntropy
variable {X I : Type*} [MeasurableSpace X] [Fintype I] [Nonempty I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

theorem entropy_integral_le_log_partition (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → I) (mg : Measurable g) (a : I → ℝ) (f : X → ℝ)
    (integrable : Integrable f μ) (δ : ℝ) (upper : ∀ x, f x ≤ a (g x)+δ) :
    entropy μ g + (∫ x, f x ∂μ) ≤ Real.log (∑ i, Real.exp (a i))+δ := by
  have total : ∑ i, μ.real (g ⁻¹' {i})=1 := by
    simpa using (integral_observation μ g mg (fun _ => (1 : ℝ))).symm
  have gibbs := LeanShared.FiniteGibbsVariational.entropy_energy_le_log_partition
    (fun i => μ.real (g ⁻¹' {i})) a (fun _ => measureReal_nonneg) total
  have intObs : Integrable (fun x => a (g x)) μ := Integrable.comp_measurable Integrable.of_finite mg
  have energy := integral_mono integrable (intObs.add (integrable_const δ)) upper
  change (∫ x, f x ∂μ) ≤ ∫ x, a (g x)+δ ∂μ at energy
  rw [integral_add intObs (integrable_const δ),integral_observation μ g mg a] at energy
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at energy
  change (∫ x, f x ∂μ) ≤ (∑ i, μ.real (g ⁻¹' {i})*a i)+δ at energy
  dsimp only [entropy]
  linarith

end LeanShared.FiniteObservationEntropy
