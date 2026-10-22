module
public import LeanShared.Dynamics.LocalPeriodicJacobian
public import Mathlib.MeasureTheory.Function.Jacobian

/-! The local regularized trace integral near a hyperbolic periodic orbit. For a
nonnegative continuous kernel `κ` supported in the `ρ`-ball and a continuous weight
`G` that is `η_G`-close to `G 0` on the relevant part of the region,
`∫_R G(w) κ(F w) dμ = (G 0 / |det(1 - P_0)|) ∫ κ dμ` up to an error
`2 (η_G + c ρ^α |G 0|) / |det(1 - P_0)| ∫ κ`, uniformly in the period and the orbit.
Change of variables through the injective closing map `F` (`MeasureTheory.Jacobian`). -/
public noncomputable section
set_option linter.unusedSectionVars false
open scoped NNReal
open MeasureTheory Set
namespace LeanShared.LocalPeriodicClosing.Data

variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace S] [BorelSpace S]
  (d : Data U S)

theorem continuous_orbit (m : ℕ) : Continuous (d.orbit m) := by
  induction m with
  | zero => exact continuous_id
  | succ m ih => exact (d.continuous m).comp ih

theorem continuous_closing : Continuous d.closing :=
  (d.continuous_orbit d.period).sub continuous_id

theorem isClosed_region : IsClosed d.region := by
  have : d.region = ⋂ m ∈ Finset.range (d.period + 1), {w | ‖d.orbit m w‖ ≤ d.r} := by
    ext w
    simp only [region, Set.mem_ofPred_eq, mem_iInter, Finset.mem_range]
    exact ⟨fun h m hm => h m (by omega), fun h m hm => h m (by omega)⟩
  rw [this]
  exact isClosed_biInter fun m _ =>
    isClosed_le (continuous_norm.comp (d.continuous_orbit m)) continuous_const

theorem abs_det_closing (w : U × S) :
    |(CyclicHyperbolicDeterminant.prodFrom (d.derivatives w) 0 d.period -
      ContinuousLinearMap.id ℝ (U × S)).det| =
    |LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) -
      CyclicHyperbolicDeterminant.prodFrom (d.derivatives w) 0 d.period) :
        (U × S) →ₗ[ℝ] (U × S))| := by
  have neg : ((CyclicHyperbolicDeterminant.prodFrom (d.derivatives w) 0 d.period -
      ContinuousLinearMap.id ℝ (U × S) : (U × S) →L[ℝ] (U × S)) : (U × S) →ₗ[ℝ] (U × S)) =
      (-1 : ℝ) • ((ContinuousLinearMap.id ℝ (U × S) -
        CyclicHyperbolicDeterminant.prodFrom (d.derivatives w) 0 d.period :
          (U × S) →L[ℝ] (U × S)) : (U × S) →ₗ[ℝ] (U × S)) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.smul_apply, neg_smul, one_smul]
    change _ - v = -(v - _)
    abel
  rw [ContinuousLinearMap.det, neg, LinearMap.det_smul, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]
  rfl

/-- The local trace integral. -/
theorem integral_estimate (k δ : ℝ≥0) (small : k + δ * 2 < 1) (K α : ℝ) (hK : 0 ≤ K)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ c ρ1 : ℝ, 0 < c ∧ 0 < ρ1 ∧ ∀ d : Data U S, d.k = k → d.δ = δ →
      (∀ i v, ‖v‖ ≤ d.r → ‖d.H' i v - d.D i‖ ≤ K * ‖v‖ ^ α) →
      ∀ (μ : Measure (U × S)) [μ.IsAddHaarMeasure] (κ : U × S → ℝ), Continuous κ →
      (∀ x, 0 ≤ κ x) → HasCompactSupport κ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ1 →
      (d.constant + 1) * ρ ≤ d.r → (∀ x, ρ < ‖x‖ → κ x = 0) →
      ∀ (G : U × S → ℝ), ContinuousOn G d.region → ∀ ηG : ℝ,
      (∀ w ∈ d.region, ‖d.closing w‖ ≤ ρ → |G w - G 0| ≤ ηG) →
      |∫ w in d.region, G w * κ (d.closing w) ∂μ -
          G 0 / |LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) -
            CyclicHyperbolicDeterminant.prodFrom d.D 0 d.period) : (U × S) →ₗ[ℝ] (U × S))| *
          ∫ x, κ x ∂μ| ≤
        2 * (ηG + c * ρ ^ α * |G 0|) / |LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) -
            CyclicHyperbolicDeterminant.prodFrom d.D 0 d.period) : (U × S) →ₗ[ℝ] (U × S))| *
          ∫ x, κ x ∂μ := by
  obtain ⟨c, ρ0, hc, hρ0, comparison⟩ := det_comparison (U := U) (S := S) k δ small K α hK hα hα1
  set ρ1 : ℝ := min ρ0 ((1 / (2 * c)) ^ α⁻¹)
  have hρ1 : 0 < ρ1 := lt_min hρ0 (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨c, ρ1, hc, hρ1, ?_⟩
  intro d hk hδ holder μ _ κ hκ hκ0 hκc ρ hρ hρ1' hρr support G hG ηG hGclose
  set J0 := |LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) -
    CyclicHyperbolicDeterminant.prodFrom d.D 0 d.period) : (U × S) →ₗ[ℝ] (U × S))|
  have hδ' : (d.δ : ℝ) = δ := by rw [hδ]
  -- the base determinant is nonzero
  have injective := CyclicHyperbolicDeterminant.injective d.A d.B d.D d.k d.δ
    (lt_of_le_of_lt (by rw [mul_two, ← add_assoc]; exact le_self_add) d.small)
    d.inverse d.stable (fun i => by simp only [D, sub_self, norm_zero, NNReal.coe_nonneg])
    d.period d.period_pos (fun i => by simp only [D, d.periodic_A, d.periodic_B])
  have J0pos : 0 < J0 := by
    apply abs_pos.mpr
    have : Function.Injective ((ContinuousLinearMap.id ℝ (U × S) -
        CyclicHyperbolicDeterminant.prodFrom d.D 0 d.period : (U × S) →L[ℝ] (U × S)) :
          (U × S) →ₗ[ℝ] (U × S)) := injective
    exact ((LinearMap.isUnit_iff_isUnit_det _).mp
      ((LinearMap.isUnit_iff_ker_eq_bot _).mpr (LinearMap.ker_eq_bot.mpr this))).ne_zero
  set F := d.closing
  set f' : U × S → (U × S) →L[ℝ] (U × S) := fun w =>
    CyclicHyperbolicDeterminant.prodFrom (d.derivatives w) 0 d.period -
      ContinuousLinearMap.id ℝ (U × S)
  have hRmeas : MeasurableSet d.region := d.isClosed_region.measurableSet
  have hF' : ∀ w ∈ d.region, HasFDerivWithinAt F (f' w) d.region w :=
    fun w hw => (d.hasFDerivAt_closing w hw).hasFDerivWithinAt
  have hinj : InjOn F d.region := d.injOn
  have hconst : 0 ≤ d.constant + 1 := by linarith [d.constant_nonneg]
  have image (x : U × S) (hx : ‖x‖ ≤ ρ) : x ∈ F '' d.region := by
    obtain ⟨w, hw, hFw⟩ := d.exists_preimage x
      ((mul_le_mul_of_nonneg_left hx hconst).trans hρr)
    exact ⟨w, hw, hFw⟩
  have κint : Integrable κ μ := hκ.integrable_of_hasCompactSupport hκc
  have total : ∫ x in F '' d.region, κ x ∂μ = ∫ x, κ x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => support x (by
      by_contra h
      push Not at h
      exact hx (image x h))
  have change := integral_image_eq_integral_abs_det_fderiv_smul μ hRmeas hF' hinj κ
  have integrableJ := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hRmeas hF'
    hinj κ).mp κint.integrableOn
  simp only [smul_eq_mul] at change integrableJ
  set a := G 0 / J0
  set η' := 2 * (ηG + c * ρ ^ α * |G 0|) / J0
  have hρα : c * ρ ^ α ≤ 1 / 2 := by
    have h1 : ρ ^ α ≤ ((1 / (2 * c)) ^ α⁻¹) ^ α :=
      Real.rpow_le_rpow hρ.le (hρ1'.trans (min_le_right _ _)) hα.le
    rw [Real.rpow_inv_rpow (by positivity) hα.ne'] at h1
    calc c * ρ ^ α ≤ c * (1 / (2 * c)) := mul_le_mul_of_nonneg_left h1 hc.le
      _ = 1 / 2 := by field_simp
  have orbit0 : ∀ m, d.orbit m (0 : U × S) = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [orbit_succ, ih, d.zero]
  have hsum : 0 ≤ ηG + c * ρ ^ α * |G 0| := by
    have hG0 : 0 ≤ ηG := by
      have := hGclose 0 (fun m _ => by rw [orbit0, norm_zero]; exact d.r_pos.le) (by
          simp only [F, closing]
          rw [orbit0, sub_zero, norm_zero]
          exact hρ.le)
      simpa only [sub_self, abs_zero] using this
    have : 0 ≤ c * ρ ^ α * |G 0| := by
      have := Real.rpow_nonneg hρ.le α
      positivity
    linarith
  have hη' : 0 ≤ η' := by positivity
  have pointwise (w : U × S) (hw : w ∈ d.region) :
      |G w * κ (F w) - a * (|(f' w).det| * κ (F w))| ≤ η' * (|(f' w).det| * κ (F w)) := by
    by_cases hb : ‖F w‖ ≤ ρ
    · obtain ⟨Rw, equation, hRw⟩ := comparison d hk hδ holder w hw
        (hb.trans (hρ1'.trans (min_le_left _ _)))
      have bα : ‖F w‖ ^ α ≤ ρ ^ α := Real.rpow_le_rpow (norm_nonneg _) hb hα.le
      have hRw' : |Rw - 1| ≤ c * ρ ^ α := hRw.trans (mul_le_mul_of_nonneg_left bα hc.le)
      have Rhalf : 1 / 2 ≤ Rw := by
        have := (abs_le.mp hRw').1
        linarith
      have Jw : |(f' w).det| = J0 * Rw := by
        rw [d.abs_det_closing w, equation, abs_mul, abs_of_pos (show (0 : ℝ) < Rw by linarith)]
      rw [Jw]
      have aJ : a * (J0 * Rw * κ (F w)) = G 0 * Rw * κ (F w) := by
        simp only [a]
        field_simp
      rw [aJ]
      have diff : |G w - G 0 * Rw| ≤ ηG + c * ρ ^ α * |G 0| := by
        have h1 := hGclose w hw hb
        have h2 : |G 0 * Rw - G 0| ≤ c * ρ ^ α * |G 0| := by
          rw [show G 0 * Rw - G 0 = G 0 * (Rw - 1) by ring, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hRw' (abs_nonneg _)
        calc |G w - G 0 * Rw| ≤ |G w - G 0| + |G 0 - G 0 * Rw| := abs_sub_le _ _ _
          _ = |G w - G 0| + |G 0 * Rw - G 0| := by rw [abs_sub_comm (G 0)]
          _ ≤ ηG + c * ρ ^ α * |G 0| := add_le_add h1 h2
      have κnn := hκ0 (F w)
      calc |G w * κ (F w) - G 0 * Rw * κ (F w)| = |G w - G 0 * Rw| * κ (F w) := by
            rw [← sub_mul, abs_mul, abs_of_nonneg κnn]
        _ ≤ (ηG + c * ρ ^ α * |G 0|) * κ (F w) := mul_le_mul_of_nonneg_right diff κnn
        _ ≤ η' * (J0 * Rw * κ (F w)) := by
            simp only [η']
            rw [div_mul_eq_mul_div, le_div_iff₀ J0pos]
            have hE : 0 ≤ (ηG + c * ρ ^ α * |G 0|) * κ (F w) := mul_nonneg hsum κnn
            nlinarith [mul_nonneg (mul_nonneg hE J0pos.le) (show (0 : ℝ) ≤ 2 * Rw - 1 by linarith)]
    · push Not at hb
      rw [support (F w) hb]
      simp only [mul_zero, sub_self, abs_zero, le_refl]
  have intG : IntegrableOn (fun w => G w * κ (F w)) d.region μ := by
    refine Integrable.mono' (integrableJ.const_mul (|a| + η'))
      ((hG.mul (hκ.comp d.continuous_closing).continuousOn).aestronglyMeasurable hRmeas)
      (ae_restrict_of_forall_mem hRmeas fun w hw => ?_)
    have h := pointwise w hw
    have J := mul_nonneg (abs_nonneg ((f' w).det)) (hκ0 (F w))
    rw [Real.norm_eq_abs]
    calc |G w * κ (F w)| ≤ |a * (|(f' w).det| * κ (F w))| + η' * (|(f' w).det| * κ (F w)) := by
          have := abs_sub_abs_le_abs_sub (G w * κ (F w)) (a * (|(f' w).det| * κ (F w)))
          linarith
      _ = (|a| + η') * (|(f' w).det| * κ (F w)) := by
          rw [abs_mul, abs_of_nonneg J]
          ring
  calc |∫ w in d.region, G w * κ (d.closing w) ∂μ - a * ∫ x, κ x ∂μ|
      = |∫ w in d.region, (G w * κ (F w) - a * (|(f' w).det| * κ (F w))) ∂μ| := by
        rw [← total, change, ← integral_const_mul, integral_sub intG (integrableJ.const_mul a)]
    _ ≤ ∫ w in d.region, η' * (|(f' w).det| * κ (F w)) ∂μ :=
        norm_integral_le_of_norm_le (integrableJ.const_mul η')
          (ae_restrict_of_forall_mem hRmeas fun w hw => by
            rw [Real.norm_eq_abs]
            exact pointwise w hw)
    _ = η' * ∫ x, κ x ∂μ := by rw [integral_const_mul, ← change, total]

end LeanShared.LocalPeriodicClosing.Data
