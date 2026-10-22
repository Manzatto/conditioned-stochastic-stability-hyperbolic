module

public import LeanShared.Probability.KernelAdjointDensity
public import LeanShared.Probability.EigenvectorMeasure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Continuous eigenmeasure density from actual kernel smoothing

A bounded measurable transition density constructs a bounded eigenmeasure
density by mixing the transition laws. Adjoint strong-Feller smoothing then
constructs a continuous representative on the live region. Existence or
continuity of the eigenmeasure density is not an input. The noise-to-density
and inverse smoothing facts themselves remain classical analytic inputs.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LeanShared.KernelEigenmeasureDensity

variable {X : Type*} [MeasurableSpace X]

section Mixture

variable (J : Kernel X X) (σ μ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure σ]
  (q : X × X → ℝ≥0∞) (hq : Measurable q)
  (hJ : ∀ x, J x = σ.withDensity (fun y => q (x, y)))

include hq hJ in
/-- Tonelli identifies the actual mixture density; no Radon--Nikodym witness
is supplied independently of the transition kernel. -/
theorem comp_eq_withDensity :
    J ∘ₘ μ = σ.withDensity (fun y => ∫⁻ x, q (x, y) ∂μ) := by
  ext A hA
  rw [Measure.bind_apply hA J.aemeasurable,
    withDensity_apply _ hA]
  simp_rw [hJ, withDensity_apply _ hA]
  exact lintegral_lintegral_swap hq.aemeasurable

include hq hJ in
/-- Nonzero left eigenvalue and bounded transition density give an actual
bounded, measurable nonnegative real eigenmeasure density. -/
theorem exists_bounded_density {r : ℝ} (hr : 0 < r)
    (hleft : J ∘ₘ μ = ENNReal.ofReal r • μ)
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hqM : ∀ x y, q (x, y) ≤ M) :
    ∃ m : X → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖m x‖ ≤ B) ∧
      μ = eigenvectorMeasure σ m := by
  let d : X → ℝ≥0∞ := fun y => ENNReal.ofReal r⁻¹ * ∫⁻ x, q (x, y) ∂μ
  have hd : Measurable d := measurable_const.mul hq.lintegral_prod_left'
  let C : ℝ≥0∞ := ENNReal.ofReal r⁻¹ * (M * μ univ)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top hM (measure_ne_top μ univ))
  have hdC (y : X) : d y ≤ C := by
    dsimp only [d, C]
    apply mul_le_mul' le_rfl
    calc
      ∫⁻ x, q (x, y) ∂μ ≤ ∫⁻ _ : X, M ∂μ := lintegral_mono (fun x => hqM x y)
      _ = M * μ univ := lintegral_const M
  have hdtop (y : X) : d y ≠ ∞ := ne_top_of_le_ne_top hC (hdC y)
  have hrepr : μ = σ.withDensity d := by
    calc
      μ = ENNReal.ofReal r⁻¹ • (J ∘ₘ μ) := by
        rw [hleft, smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),
          inv_mul_cancel₀ hr.ne', ENNReal.ofReal_one, one_smul]
      _ = ENNReal.ofReal r⁻¹ • σ.withDensity (fun y => ∫⁻ x, q (x, y) ∂μ) := by
        rw [comp_eq_withDensity J σ μ q hq hJ]
      _ = σ.withDensity d := (withDensity_smul _ hq.lintegral_prod_left').symm
  refine ⟨fun y => (d y).toReal, hd.ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩, ?_⟩
  · intro y
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hC (hdC y)
  · rw [hrepr]
    unfold eigenvectorMeasure
    congr 1
    funext y
    exact (ENNReal.ofReal_toReal (hdtop y)).symm

end Mixture

section Smoothing

variable [TopologicalSpace X]

/-- The inverse integral of the bounded density gives a continuous
representative. Only actual kernel density and inverse smoothing are inputs. -/
theorem exists_continuousOn_density
    (J L : Kernel X X) [IsFiniteKernel L] (σ μ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure σ]
    (q : X × X → ℝ≥0∞) (hq : Measurable q)
    (hJ : ∀ x, J x = σ.withDensity (fun y => q (x, y)))
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hqM : ∀ x y, q (x, y) ≤ M)
    (hdual : KernelAdjointDensity.IsAdjoint J L σ)
    (K : Set X)
    (hSF : ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) →
      ContinuousOn (fun x => ∫ y, f y ∂L x) K)
    {r : ℝ} (hr : 0 < r) (hleft : J ∘ₘ μ = ENNReal.ofReal r • μ) :
    ∃ m : X → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧ ContinuousOn m K ∧
      μ = eigenvectorMeasure σ m := by
  obtain ⟨m, hm, hm0, hb, hrepr⟩ := exists_bounded_density J σ μ q hq hJ hr hleft M hM hqM
  obtain ⟨B, hB, hmB⟩ := hb
  have hint (x : X) : Integrable m (L x) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hmB)
  have hleft' := hleft
  rw [hrepr] at hleft'
  have hharm := KernelAdjointDensity.real_density_eigen_ae J L σ hdual m hm hm0 r hr.le
    (by simpa only [eigenvectorMeasure] using hleft') (ae_of_all _ hint)
  let n : X → ℝ := fun x => r⁻¹ * ∫ y, m y ∂L x
  have hn : Measurable n := measurable_const.mul
    (hm.stronglyMeasurable.integral_kernel (κ := L)).measurable
  have hn0 (x : X) : 0 ≤ n x := mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg hm0)
  have heq : m =ᵐ[σ] n := by
    filter_upwards [hharm] with x hx
    change m x = r⁻¹ * ∫ y, m y ∂L x
    rw [hx, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  refine ⟨n, hn, hn0, (hSF m hm ⟨B, hB, hmB⟩).const_mul r⁻¹, ?_⟩
  rw [hrepr]
  exact withDensity_congr_ae (heq.fun_comp ENNReal.ofReal)

variable [BorelSpace X] [T2Space X]

/-- Compact killing turns continuous-on-live densities into bounded tests
for the actual inverse smoother. No global continuous extension is used. -/
theorem continuousOn_integral_of_compact_killing
    (L : Kernel X X) (K : Set X) (hK : IsCompact K)
    (hLS : ∀ x ∈ K, (L x).restrict K = L x)
    (hSF : ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) →
      ContinuousOn (fun x => ∫ y, f y ∂L x) K)
    (m : X → ℝ) (hm : Measurable m) (hmc : ContinuousOn m K) :
    ContinuousOn (fun x => ∫ y, m y ∂L x) K := by
  classical
  obtain ⟨B, hB⟩ := hK.bddAbove_image hmc.norm
  let g := K.indicator m
  have hg : Measurable g := hm.indicator hK.measurableSet
  have hb : ∀ x, ‖g x‖ ≤ max B 0 := by
    intro x
    by_cases hx : x ∈ K
    · rw [show g x = m x from indicator_of_mem hx m]
      exact (hB (mem_image_of_mem (fun y => ‖m y‖) hx)).trans (le_max_left _ _)
    · rw [show g x = 0 from indicator_of_notMem hx m, norm_zero]
      exact le_max_right _ _
  apply (hSF g hg ⟨max B 0, le_max_right _ _, hb⟩).congr
  intro x hx
  apply integral_congr_ae
  have ha : ∀ᵐ y ∂L x, y ∈ K := by
    rw [← hLS x hx]
    exact ae_restrict_mem hK.measurableSet
  exact ha.mono (fun y hy => (indicator_of_mem hy m).symm)

/-- Bounded actual noise densities, inverse smoothing and compact killing
construct a continuous density and its pointwise inverse eigenrelation.
Both regularity conclusions in the inverse-positivity certificate are derived. -/
theorem exists_continuous_harmonic_density
    (J L : Kernel X X) [IsFiniteKernel L] (σ μ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure σ] [σ.Regular]
    (q : X × X → ℝ≥0∞) (hq : Measurable q)
    (hJ : ∀ x, J x = σ.withDensity (fun y => q (x, y)))
    (M : ℝ≥0∞) (hM : M ≠ ∞) (hqM : ∀ x y, q (x, y) ≤ M)
    (hdual : KernelAdjointDensity.IsAdjoint J L σ)
    (K : Set X) (hK : IsCompact K) (hsupport : σ.support = K)
    (hLS : ∀ x ∈ K, (L x).restrict K = L x)
    (hSF : ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) →
      ContinuousOn (fun x => ∫ y, f y ∂L x) K)
    {r : ℝ} (hr : 0 < r) (hleft : J ∘ₘ μ = ENNReal.ofReal r • μ) :
    ∃ m : X → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧ ContinuousOn m K ∧
      μ = eigenvectorMeasure σ m ∧
      ContinuousOn (fun x => ∫ y, m y ∂L x) K ∧
      ∀ x ∈ K, (∫ y, m y ∂L x) = r * m x := by
  obtain ⟨m, hm, hm0, hmc, hrepr⟩ := exists_continuousOn_density
    J L σ μ q hq hJ M hM hqM hdual K hSF hr hleft
  have himage := continuousOn_integral_of_compact_killing L K hK hLS hSF m hm hmc
  have hleft' := hleft
  rw [hrepr] at hleft'
  refine ⟨m, hm, hm0, hmc, hrepr, himage, ?_⟩
  exact KernelAdjointDensity.real_density_eigen_on_compact J L σ hdual K hK hsupport
    hLS m hm hm0 r hr.le hleft' hmc himage

end Smoothing

end LeanShared.KernelEigenmeasureDensity
