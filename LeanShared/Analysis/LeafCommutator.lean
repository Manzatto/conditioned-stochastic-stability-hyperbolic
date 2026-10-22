module
public import LeanShared.Analysis.ConeKernelMoments
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.LIntegral

/-! Commutators of convolution with multiplication. For a Schwartz kernel `K`, a Schwartz multiplier
`a` and a Schwartz input `u`, `K * (a u) = a (K * u) + [K*, a] u` with `[K*, a] u (x) = ∫ K(x -
y) (a(y) - a(x)) u(y) dy`. On a translation-closed family of leaf measures, leafwise Young
bounds the commutator by the Lipschitz constant of `a` times the first kernel moment; for a
derivative input `∂_v G` an integration by parts moves the derivative onto the kernel and the
multiplier. -/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped SchwartzMap ENNReal
namespace LeanShared.LeafCommutator

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Leafwise Young inequality on a translation-closed family of measures. -/
theorem young (ν : Measure E) [SFinite ν] (family : A → Measure E)
    (translate : ∀ z : E, ∃ a, ν.map (fun x => x + z) = family a)
    (k f : E → ℝ≥0∞) (mk : Measurable k) (mf : Measurable f) :
    (∫⁻ x, (∫⁻ z, k z * f (x - z)) ∂ν) ≤ (∫⁻ z, k z) * ⨆ a, ∫⁻ x, f x ∂family a := by
  have translated (z : E) : (∫⁻ x, f (x - z) ∂ν) ≤ ⨆ a, ∫⁻ x, f x ∂family a := by
    obtain ⟨a, ha⟩ := translate (-z)
    have actual := lintegral_map (μ := ν) (f := f) (g := fun x : E => x + -z) mf
      (continuous_id.add continuous_const).measurable
    rw [ha] at actual
    simp only [sub_eq_add_neg]
    rw [← actual]
    exact le_iSup (fun a => ∫⁻ x, f x ∂family a) a
  have joint : Measurable (fun p : E × E => k p.2 * f (p.1 - p.2)) :=
    (mk.comp measurable_snd).mul (mf.comp (measurable_fst.sub measurable_snd))
  rw [lintegral_lintegral_swap joint.aemeasurable]
  calc _ ≤ ∫⁻ z, k z * ⨆ a, ∫⁻ x, f x ∂family a := by
        apply lintegral_mono
        intro z
        change (∫⁻ x, k z * f (x - z) ∂ν) ≤ k z * ⨆ a, ∫⁻ x, f x ∂family a
        rw [lintegral_const_mul (k z) (f := fun x => f (x - z))
          (mf.comp (measurable_id.sub measurable_const))]
        gcongr
        exact translated z
    _ = _ := lintegral_mul_const _ mk

/-- The commutator `[K*, a] u`. -/
@[expose] def comm (K a u : E → ℂ) (x : E) : ℂ := ∫ y, K (x - y) * ((a y - a x) * u y)

/-- The Schwartz product. -/
@[expose] def mul (a u : 𝓢(E, ℂ)) : 𝓢(E, ℂ) := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) a u

theorem mul_apply (a u : 𝓢(E, ℂ)) (x : E) : mul a u x = a x * u x := by
  rw [mul, SchwartzMap.pairing_apply_apply]
  rfl

theorem exists_bound (K : 𝓢(E, ℂ)) : ∃ C : ℝ, ∀ x, ‖K x‖ ≤ C :=
  ⟨_, fun x => SchwartzMap.norm_le_seminorm ℝ K x⟩

theorem translate_integrable (K w : 𝓢(E, ℂ)) (x : E) :
    Integrable (fun y => K (x - y) * w y) := by
  obtain ⟨C, hC⟩ := exists_bound K
  exact w.integrable.bdd_mul (c := C)
    (K.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => hC (x - y))

theorem comm_integrable (K a u : 𝓢(E, ℂ)) (x : E) :
    Integrable (fun y => K (x - y) * ((a y - a x) * u y)) := by
  have h1 := translate_integrable K (mul a u) x
  have h2 := (translate_integrable K u x).const_mul (a x)
  refine (h1.sub h2).congr (ae_of_all _ fun y => ?_)
  simp only [Pi.sub_apply, mul_apply]
  ring

/-- The block of a product is the product of the block plus the commutator. -/
theorem block_mul (σ a u : 𝓢(E, ℂ)) (x : E) :
    ConeFourierBlocks.block σ (mul a u) x =
      a x * ConeFourierBlocks.block σ u x + comm (FourierSchwartzKernel.kernel σ) a u x := by
  rw [ConeFourierBlocks.block_apply, ConeFourierBlocks.block_apply, comm,
    ← integral_const_mul, ← integral_add
      ((translate_integrable (FourierSchwartzKernel.kernel σ) u x).const_mul (a x))
      (comm_integrable (FourierSchwartzKernel.kernel σ) a u x)]
  congr 1
  funext y
  rw [mul_apply]
  ring

theorem lintegral_moment (K : 𝓢(E, ℂ)) :
    (∫⁻ z, ‖z‖ₑ * ‖K z‖ₑ) = ENNReal.ofReal (∫ z, ‖z‖ * ‖K z‖) := by
  rw [ofReal_integral_eq_lintegral_ofReal (ConeKernelMoments.moment_integrable K)
    (ae_of_all _ fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  congr 1
  funext z
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- The pointwise commutator bound for a Lipschitz multiplier. -/
theorem comm_enorm_le (K a u : 𝓢(E, ℂ)) {L : ℝ} (hL : 0 ≤ L)
    (lip : ∀ x y, ‖a x - a y‖ ≤ L * ‖x - y‖) (x : E) :
    ‖comm K a u x‖ₑ ≤ ENNReal.ofReal L * ∫⁻ z, ‖z‖ₑ * ‖K z‖ₑ * ‖u (x - z)‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_sub_left_eq_self (fun z => ENNReal.ofReal L * (‖z‖ₑ * ‖K z‖ₑ * ‖u (x - z)‖ₑ)) x]
  apply lintegral_mono
  intro y
  simp only [sub_sub_cancel]
  have hy : ‖a y - a x‖ₑ ≤ ENNReal.ofReal L * ‖x - y‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hL]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_sub_rev (a y)]
    exact lip x y
  rw [enorm_mul, enorm_mul]
  calc ‖K (x - y)‖ₑ * (‖a y - a x‖ₑ * ‖u y‖ₑ)
      ≤ ‖K (x - y)‖ₑ * ((ENNReal.ofReal L * ‖x - y‖ₑ) * ‖u y‖ₑ) := by gcongr
    _ = ENNReal.ofReal L * (‖x - y‖ₑ * ‖K (x - y)‖ₑ * ‖u y‖ₑ) := by ring

/-- The leafwise commutator bound: Lipschitz constant times first kernel moment. -/
theorem leaf_comm_le (ν : Measure E) [SFinite ν] (family : A → Measure E)
    (translate : ∀ z : E, ∃ a, ν.map (fun x => x + z) = family a)
    (K a u : 𝓢(E, ℂ)) {L : ℝ} (hL : 0 ≤ L) (lip : ∀ x y, ‖a x - a y‖ ≤ L * ‖x - y‖) :
    (∫⁻ x, ‖comm K a u x‖ₑ ∂ν) ≤ ENNReal.ofReal L * ENNReal.ofReal (∫ z, ‖z‖ * ‖K z‖) *
      ⨆ b, ∫⁻ x, ‖u x‖ₑ ∂family b := by
  calc (∫⁻ x, ‖comm K a u x‖ₑ ∂ν)
      ≤ ∫⁻ x, ENNReal.ofReal L * (∫⁻ z, ‖z‖ₑ * ‖K z‖ₑ * ‖u (x - z)‖ₑ) ∂ν :=
        lintegral_mono fun x => comm_enorm_le K a u hL lip x
    _ = ENNReal.ofReal L * ∫⁻ x, (∫⁻ z, (‖z‖ₑ * ‖K z‖ₑ) * ‖u (x - z)‖ₑ) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal L * ((∫⁻ z, ‖z‖ₑ * ‖K z‖ₑ) * ⨆ b, ∫⁻ x, ‖u x‖ₑ ∂family b) := by
        gcongr
        exact young ν family translate _ _ (measurable_id.enorm.mul K.continuous.measurable.enorm)
          u.continuous.measurable.enorm
    _ = _ := by rw [lintegral_moment, mul_assoc]

end LeanShared.LeafCommutator
