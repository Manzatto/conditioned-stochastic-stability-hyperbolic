module
public import LeanShared.Analysis.LeafCommutator

/-! The commutator on a derivative input. Integrating by parts, `[K*, a] (∂_v G)(x) = ∫ (∂_v K(x -
y) (a(y) - a(x)) - K(x - y) ∂_v a(y)) G(y) dy`, so on a translation-closed leaf family the
commutator of a derivative is bounded by the derivative moment of `K` and the mass of `K` times
the leaf size of `G`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped SchwartzMap ENNReal
open LineDeriv
namespace LeanShared.LeafCommutator

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_fderiv_bound (K : 𝓢(E, ℂ)) : ∃ C : ℝ, ∀ x, ‖fderiv ℝ K x‖ ≤ C :=
  ⟨_, fun x => by
    simpa only [SchwartzMap.fderivCLM_apply] using
      SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.fderivCLM ℝ E ℂ K) x⟩

theorem bounded_mul_integrable {φ : E → ℂ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C)
    {g : E → ℂ} (hg : Integrable g) : Integrable (fun y => φ y * g y) :=
  hg.bdd_mul (c := C) hφ.aestronglyMeasurable (ae_of_all _ hC)

/-- The derivative of the integration-by-parts weight `y ↦ K(x - y) (a(y) - a(x))`. -/
theorem weight_hasFDerivAt (K a : 𝓢(E, ℂ)) (x y : E) :
    HasFDerivAt (fun y => K (x - y) * (a y - a x))
      (K (x - y) • fderiv ℝ a y +
        (a y - a x) • ((fderiv ℝ K (x - y)).comp (-ContinuousLinearMap.id ℝ E))) y := by
  have h1 : HasFDerivAt (fun y => K (x - y))
      ((fderiv ℝ K (x - y)).comp (-ContinuousLinearMap.id ℝ E)) y := by
    have inner : HasFDerivAt (fun y : E => x - y) (-ContinuousLinearMap.id ℝ E) y := by
      exact (hasFDerivAt_id y).const_sub x
    exact (K.differentiableAt.hasFDerivAt).comp y inner
  have h2 : HasFDerivAt (fun y => a y - a x) (fderiv ℝ a y) y :=
    a.differentiableAt.hasFDerivAt.sub_const _
  exact h1.mul h2

theorem weight_fderiv_apply (K a : 𝓢(E, ℂ)) (x y v : E) :
    fderiv ℝ (fun y => K (x - y) * (a y - a x)) y v =
      K (x - y) * fderiv ℝ a y v - fderiv ℝ K (x - y) v * (a y - a x) := by
  rw [(weight_hasFDerivAt K a x y).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg, smul_eq_mul]
  ring

/-- Integration by parts for the commutator of a derivative input. -/
theorem comm_lineDeriv (K a G : 𝓢(E, ℂ)) (v x : E) :
    comm K a (fun y => fderiv ℝ G y v) x =
      ∫ y, (fderiv ℝ K (x - y) v * (a y - a x) - K (x - y) * fderiv ℝ a y v) * G y := by
  obtain ⟨CK, hCK⟩ := exists_bound K
  obtain ⟨Ca, hCa⟩ := exists_bound a
  obtain ⟨CDK, hCDK⟩ := exists_fderiv_bound K
  obtain ⟨CDa, hCDa⟩ := exists_fderiv_bound a
  have Kcont : Continuous (fun y => K (x - y)) := K.continuous.comp (continuous_const.sub continuous_id)
  have DKcont : Continuous (fun y => fderiv ℝ K (x - y) v) :=
    ((SchwartzMap.fderivCLM ℝ E ℂ K).continuous.comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const
  have Dacont : Continuous (fun y => fderiv ℝ a y v) :=
    (SchwartzMap.fderivCLM ℝ E ℂ a).continuous.clm_apply continuous_const
  have weightCont : Continuous (fun y => K (x - y) * (a y - a x)) :=
    Kcont.mul (a.continuous.sub continuous_const)
  have weightBound : ∀ y, ‖K (x - y) * (a y - a x)‖ ≤ CK * (Ca + Ca) := fun y => by
    rw [norm_mul]
    exact mul_le_mul (hCK _) ((norm_sub_le _ _).trans (add_le_add (hCa _) (hCa _)))
      (norm_nonneg _) ((norm_nonneg _).trans (hCK 0))
  have derivFormula : (fun y => fderiv ℝ (fun y => K (x - y) * (a y - a x)) y v) =
      fun y => K (x - y) * fderiv ℝ a y v - fderiv ℝ K (x - y) v * (a y - a x) :=
    funext fun y => weight_fderiv_apply K a x y v
  have derivBound : ∀ y, ‖K (x - y) * fderiv ℝ a y v - fderiv ℝ K (x - y) v * (a y - a x)‖ ≤
      CK * (CDa * ‖v‖) + CDK * ‖v‖ * (Ca + Ca) := fun y => by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (hCK _) (((fderiv ℝ a y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hCDa y) (norm_nonneg _))) (norm_nonneg _)
        ((norm_nonneg _).trans (hCK 0))
    · rw [norm_mul]
      exact mul_le_mul (((fderiv ℝ K (x - y)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hCDK _) (norm_nonneg _)))
        ((norm_sub_le _ _).trans (add_le_add (hCa _) (hCa _))) (norm_nonneg _)
        (mul_nonneg ((norm_nonneg _).trans (hCDK 0)) (norm_nonneg _))
  have lineG : Integrable (fun y => fderiv ℝ G y v) := by
    refine (∂_{v} G).integrable.congr (ae_of_all _ fun y => ?_)
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv v G y
  have hf'g : Integrable (fun y => fderiv ℝ (fun y => K (x - y) * (a y - a x)) y v * G y) := by
    simp only [weight_fderiv_apply]
    exact bounded_mul_integrable ((Kcont.mul Dacont).sub (DKcont.mul
      (a.continuous.sub continuous_const))) derivBound G.integrable
  have hfg' : Integrable (fun y => K (x - y) * (a y - a x) * fderiv ℝ G y v) :=
    bounded_mul_integrable weightCont weightBound lineG
  have hfg : Integrable (fun y => K (x - y) * (a y - a x) * G y) :=
    bounded_mul_integrable weightCont weightBound G.integrable
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun y _ => (weight_hasFDerivAt K a x y).differentiableAt) (fun y _ => G.differentiableAt)
  simp only [weight_fderiv_apply] at ibp
  calc comm K a (fun y => fderiv ℝ G y v) x
      = ∫ y, K (x - y) * (a y - a x) * fderiv ℝ G y v := by
        unfold comm
        congr 1
        funext y
        ring
    _ = -∫ y, (K (x - y) * fderiv ℝ a y v - fderiv ℝ K (x - y) v * (a y - a x)) * G y := ibp
    _ = _ := by
        rw [← integral_neg]
        congr 1
        funext y
        ring

/-- The pointwise bound for the commutator of a derivative input. -/
theorem comm_lineDeriv_enorm_le (K a G : 𝓢(E, ℂ)) (v : E) {L D : ℝ} (hL : 0 ≤ L)
    (lip : ∀ x y, ‖a x - a y‖ ≤ L * ‖x - y‖) (deriv : ∀ y, ‖fderiv ℝ a y v‖ ≤ D) (x : E) :
    ‖comm K a (fun y => fderiv ℝ G y v) x‖ₑ ≤
      ∫⁻ z, (ENNReal.ofReal L * ‖v‖ₑ * (‖fderiv ℝ K z‖ₑ * ‖z‖ₑ) + ENNReal.ofReal D * ‖K z‖ₑ) *
        ‖G (x - z)‖ₑ := by
  rw [comm_lineDeriv]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_sub_left_eq_self (fun z => (ENNReal.ofReal L * ‖v‖ₑ * (‖fderiv ℝ K z‖ₑ * ‖z‖ₑ) +
    ENNReal.ofReal D * ‖K z‖ₑ) * ‖G (x - z)‖ₑ) x]
  apply lintegral_mono
  intro y
  simp only [sub_sub_cancel]
  have hy : ‖a y - a x‖ₑ ≤ ENNReal.ofReal L * ‖x - y‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hL]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_sub_rev (a y)]
    exact lip x y
  have hDK : ‖fderiv ℝ K (x - y) v‖ₑ ≤ ‖fderiv ℝ K (x - y)‖ₑ * ‖v‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal ((fderiv ℝ K (x - y)).le_opNorm v)
  have hDa : ‖fderiv ℝ a y v‖ₑ ≤ ENNReal.ofReal D := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (deriv y)
  rw [enorm_mul]
  gcongr
  refine (enorm_sub_le).trans ?_
  rw [enorm_mul, enorm_mul]
  calc ‖fderiv ℝ K (x - y) v‖ₑ * ‖a y - a x‖ₑ + ‖K (x - y)‖ₑ * ‖fderiv ℝ a y v‖ₑ
      ≤ ‖fderiv ℝ K (x - y)‖ₑ * ‖v‖ₑ * (ENNReal.ofReal L * ‖x - y‖ₑ) +
          ‖K (x - y)‖ₑ * ENNReal.ofReal D := by gcongr
    _ = ENNReal.ofReal L * ‖v‖ₑ * (‖fderiv ℝ K (x - y)‖ₑ * ‖x - y‖ₑ) +
          ENNReal.ofReal D * ‖K (x - y)‖ₑ := by ring

theorem lintegral_derivative_moment (K : 𝓢(E, ℂ)) :
    (∫⁻ z, ‖fderiv ℝ K z‖ₑ * ‖z‖ₑ) = ENNReal.ofReal (∫ z, ‖fderiv ℝ K z‖ * ‖z‖) := by
  rw [ofReal_integral_eq_lintegral_ofReal (ConeKernelMoments.derivative_moment_integrable K)
    (ae_of_all _ fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  congr 1
  funext z
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

theorem lintegral_mass (K : 𝓢(E, ℂ)) : (∫⁻ z, ‖K z‖ₑ) = ENNReal.ofReal (∫ z, ‖K z‖) :=
  (ofReal_integral_norm_eq_lintegral_enorm K.integrable).symm

/-- The leafwise bound for the commutator of a derivative input. -/
theorem leaf_comm_lineDeriv_le (ν : Measure E) [SFinite ν] (family : A → Measure E)
    (translate : ∀ z : E, ∃ a, ν.map (fun x => x + z) = family a)
    (K a G : 𝓢(E, ℂ)) (v : E) {L D : ℝ} (hL : 0 ≤ L)
    (lip : ∀ x y, ‖a x - a y‖ ≤ L * ‖x - y‖) (deriv : ∀ y, ‖fderiv ℝ a y v‖ ≤ D) :
    (∫⁻ x, ‖comm K a (fun y => fderiv ℝ G y v) x‖ₑ ∂ν) ≤
      (ENNReal.ofReal L * ‖v‖ₑ * ENNReal.ofReal (∫ z, ‖fderiv ℝ K z‖ * ‖z‖) +
        ENNReal.ofReal D * ENNReal.ofReal (∫ z, ‖K z‖)) * ⨆ b, ∫⁻ x, ‖G x‖ₑ ∂family b := by
  have mk : Measurable (fun z => ENNReal.ofReal L * ‖v‖ₑ * (‖fderiv ℝ K z‖ₑ * ‖z‖ₑ) +
      ENNReal.ofReal D * ‖K z‖ₑ) := by
    have dK : Measurable (fun z => fderiv ℝ K z) :=
      (SchwartzMap.fderivCLM ℝ E ℂ K).continuous.measurable
    exact (measurable_const.mul (dK.enorm.mul measurable_id.enorm)).add
      (measurable_const.mul K.continuous.measurable.enorm)
  calc (∫⁻ x, ‖comm K a (fun y => fderiv ℝ G y v) x‖ₑ ∂ν)
      ≤ ∫⁻ x, (∫⁻ z, (ENNReal.ofReal L * ‖v‖ₑ * (‖fderiv ℝ K z‖ₑ * ‖z‖ₑ) +
          ENNReal.ofReal D * ‖K z‖ₑ) * ‖G (x - z)‖ₑ) ∂ν :=
        lintegral_mono fun x => comm_lineDeriv_enorm_le K a G v hL lip deriv x
    _ ≤ (∫⁻ z, ENNReal.ofReal L * ‖v‖ₑ * (‖fderiv ℝ K z‖ₑ * ‖z‖ₑ) + ENNReal.ofReal D * ‖K z‖ₑ) *
          ⨆ b, ∫⁻ x, ‖G x‖ₑ ∂family b :=
        young ν family translate _ _ mk G.continuous.measurable.enorm
    _ = _ := by
        have dK : Measurable (fun z => fderiv ℝ K z) :=
          (SchwartzMap.fderivCLM ℝ E ℂ K).continuous.measurable
        rw [lintegral_add_left (f := fun z => ENNReal.ofReal L * ‖v‖ₑ * (‖fderiv ℝ K z‖ₑ * ‖z‖ₑ))
            (measurable_const.mul (dK.enorm.mul measurable_id.enorm)),
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_derivative_moment, lintegral_mass]

end LeanShared.LeafCommutator
