module

public import LeanShared.Probability.KernelEigenmeasureDensity

/-! # Continuous harmonic density without full support on the live set

A closed killed layer can have reference-null boundary pieces. Absolute
continuity of the actual inverse transition transports equality of densities
almost everywhere and gives the harmonic law at every live point, without
assuming that the reference measure supports the whole closed layer.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace LeanShared.KernelEigenmeasureDensity
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

theorem exists_continuous_harmonic_density_of_inverse_ac
    (J L : Kernel X X) [IsFiniteKernel L] (σ μ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure σ]
    (q : X × X → ℝ≥0∞) (hq : Measurable q)
    (hJ : ∀ x, J x = σ.withDensity (fun y => q (x, y)))
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hqM : ∀ x y, q (x, y) ≤ M)
    (hdual : KernelAdjointDensity.IsAdjoint J L σ) (K : Set X)
    (hac : ∀ x ∈ K, L x ≪ σ)
    (hSF : ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) →
      ContinuousOn (fun x => ∫ y, f y ∂L x) K)
    {r : ℝ} (hr : 0 < r) (hleft : J ∘ₘ μ = ENNReal.ofReal r • μ) :
    ∃ m : X → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧ ContinuousOn m K ∧
      μ = eigenvectorMeasure σ m ∧
      ContinuousOn (fun x => ∫ y, m y ∂L x) K ∧
      ∀ x ∈ K, (∫ y, m y ∂L x) = r * m x := by
  obtain ⟨m₀, hm₀, hm₀0, ⟨B, hB, hm₀B⟩, hrepr⟩ :=
    exists_bounded_density J σ μ q hq hJ hr hleft M hM hqM
  have hint (x : X) : Integrable m₀ (L x) :=
    Integrable.of_bound hm₀.aestronglyMeasurable B (ae_of_all _ hm₀B)
  have hleft' := hleft
  rw [hrepr] at hleft'
  have hAE := KernelAdjointDensity.real_density_eigen_ae J L σ hdual m₀ hm₀ hm₀0 r hr.le
    (by simpa only [eigenvectorMeasure] using hleft') (ae_of_all _ hint)
  let m : X → ℝ := fun x => r⁻¹ * ∫ y, m₀ y ∂L x
  have hm : Measurable m := measurable_const.mul
    (hm₀.stronglyMeasurable.integral_kernel (κ := L)).measurable
  have hm0 : ∀ x, 0 ≤ m x := fun x => mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg hm₀0)
  have hmc : ContinuousOn m K := (hSF m₀ hm₀ ⟨B, hB, hm₀B⟩).const_mul r⁻¹
  have heq : m₀ =ᵐ[σ] m := by
    filter_upwards [hAE] with x hx
    change m₀ x = r⁻¹ * ∫ y, m₀ y ∂L x
    rw [hx, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hpoint : ∀ x ∈ K, (∫ y, m y ∂L x) = r * m x := by
    intro x hx
    rw [integral_congr_ae ((hac x hx).ae_eq heq).symm]
    change (∫ y, m₀ y ∂L x) = r * (r⁻¹ * ∫ y, m₀ y ∂L x)
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  refine ⟨m, hm, hm0, hmc, ?_, ?_, hpoint⟩
  · rw [hrepr]
    exact withDensity_congr_ae (heq.fun_comp ENNReal.ofReal)
  · exact (hmc.const_mul r).congr (fun x hx => hpoint x hx)

end LeanShared.KernelEigenmeasureDensity
