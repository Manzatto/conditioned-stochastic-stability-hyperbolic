module
public import LeanShared.Analysis.ConvolutionBlockBound
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Block norm calculus on a translation-closed leaf family. If
`g(x) = Σ_k ∫ a_k(p) f_k(x - φ(p)) dν(p)`, the block core norm of `g` is at most
`Σ_k ‖a_k‖₁ ‖f_k‖`. Consequences: translation does not increase the norm, a translation
difference is bounded by the directional derivative, and mollification converges with
rate `ε Σ_k ‖∂_k f‖`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped SchwartzMap ENNReal Topology
namespace LeanShared.BlockNormCalculus
open FourierSchwartzKernel SchwartzJetSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A Fourier block of a translation family is the translation family of the block. -/
theorem block_family {P : Type*} [MeasurableSpace P] (ν : Measure P) [SFinite ν]
    (σ : 𝓢(E, ℂ)) (a : P → ℂ) (ha : Integrable a ν) (am : Measurable a)
    (φ : P → E) (hφ : Measurable φ) (f : 𝓢(E, ℂ)) (x : E) :
    ∫ y, kernel σ (x - y) * ∫ p, a p * f (y - φ p) ∂ν =
      ∫ p, a p * ConeFourierBlocks.block σ f (x - φ p) ∂ν := by
  obtain ⟨C, hC⟩ := LeafCommutator.exists_bound f
  have product : Integrable (fun q : E × P => kernel σ (x - q.1) * (a q.2 * f (q.1 - φ q.2)))
      (volume.prod ν) := by
    have base : Integrable (fun q : E × P => ‖kernel σ (x - q.1)‖ * (‖a q.2‖ * C))
        (volume.prod ν) :=
      ((kernel σ).integrable.comp_sub_left x).norm.mul_prod (ha.norm.mul_const C)
    refine base.mono' ?_ (ae_of_all _ fun q => ?_)
    · exact (((kernel σ).continuous.comp (continuous_const.sub continuous_id)).measurable.comp
        measurable_fst).aestronglyMeasurable.mul
        ((am.comp measurable_snd).mul (f.continuous.measurable.comp
          (measurable_fst.sub (hφ.comp measurable_snd)))).aestronglyMeasurable
    · rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
        (norm_nonneg _)
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap product]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only
  rw [ConeFourierBlocks.block_apply, ← integral_const_mul]
  have shift := integral_sub_right_eq_self (μ := volume)
    (fun y => a p * (kernel σ (x - φ p - y) * f y)) (φ p)
  rw [← shift]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [show x - φ p - (y - φ p) = x - y by abel]
  ring

/-- The fundamental theorem of calculus along a segment. -/
theorem ftc_line (f : 𝓢(E, ℂ)) (x z : E) :
    f (x - z) - f x = ∫ τ in Ioc (0 : ℝ) 1, -(fderiv ℝ f (x - τ • z) z) := by
  have deriv (τ : ℝ) : HasDerivAt (fun τ : ℝ => f (x - τ • z)) (-(fderiv ℝ f (x - τ • z) z)) τ := by
    have inner : HasDerivAt (fun τ : ℝ => x - τ • z) (-z) τ := by
      simpa only [one_smul, zero_sub, id] using ((hasDerivAt_id τ).smul_const z).const_sub x
    have outer := (f.differentiableAt (x := x - τ • z)).hasFDerivAt.comp_hasDerivAt τ inner
    exact outer.congr_deriv (by rw [map_neg])
  have cont : Continuous (fun τ : ℝ => -(fderiv ℝ f (x - τ • z) z)) :=
    (((f.smooth ⊤).continuous_fderiv (by simp)).comp (continuous_const.sub
      (continuous_id.smul continuous_const))).clm_apply continuous_const |>.neg
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => deriv τ)
      (cont.intervalIntegrable 0 1)]
  simp only [one_smul, zero_smul, sub_zero]

section Main
variable {U A S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (σ : ℕ × S → 𝓢(E, ℂ)) (t : S → ℝ)

/-- The master estimate for finite sums of translation families. -/
theorem family_bound [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    {ι : Type*} [Fintype ι] {P : Type*} [MeasurableSpace P] (ν : Measure P) [SFinite ν]
    (a : ι → P → ℂ) (ha : ∀ k, Integrable (a k) ν) (am : ∀ k, Measurable (a k))
    (φ : P → E) (hφ : Measurable φ)
    {D : ι → Set E} (bD : ∀ k, SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves (D k) σ t)
    {D' : Set E} (bD' : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D' σ t)
    (f : ∀ k, supportedCore (D k)) (g : supportedCore D')
    (hg : ∀ x, g.val x = ∑ k, ∫ p, a k p * (f k).val (x - φ p) ∂ν) :
    ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D' σ t bD' g‖ ≤
      ∑ k, (∫ p, ‖a k p‖ ∂ν) * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves (D k) σ t (bD k) (f k)‖ := by
  set A0 : ι → ℝ := fun k => ‖SchwartzAmbientBlocks.coreMap μ hJ leaves (D k) σ t (bD k) (f k)‖
  set R : ι → ℝ := fun k => ∫ p, ‖a k p‖ ∂ν
  have A0nn (k : ι) : 0 ≤ A0 k := norm_nonneg _
  have Rnn (k : ι) : 0 ≤ R k := integral_nonneg fun _ => norm_nonneg _
  set Tot := ∑ k, R k * A0 k with hTot
  have Totnn : 0 ≤ Tot := Finset.sum_nonneg fun k _ => mul_nonneg (Rnn k) (A0nn k)
  rw [SchwartzAmbientBlocks.coreMap_norm]
  refine Real.iSup_le (fun j => ?_) Totnn
  obtain ⟨n, s⟩ := j
  have pow_pos' : (0 : ℝ) < (2 : ℝ) ^ (t s * n) := Real.rpow_pos_of_pos (by norm_num) _
  let family : A → Measure E := fun c => (leaves c).measure μ
  set K := ConeFourierBlocks.block (σ (n, s))
  have integrableK (k : ι) (x : E) :
      Integrable (fun y => kernel (σ (n, s)) (x - y) * ∫ p, a k p * (f k).val (y - φ p) ∂ν) := by
    obtain ⟨C, hC⟩ := LeafCommutator.exists_bound (f k).val
    have inner (y : E) : ‖∫ p, a k p * (f k).val (y - φ p) ∂ν‖ ≤ R k * C := by
      refine (norm_integral_le_integral_norm _).trans ?_
      calc ∫ p, ‖a k p * (f k).val (y - φ p)‖ ∂ν ≤ ∫ p, ‖a k p‖ * C ∂ν := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              ((ha k).norm.mul_const C) (ae_of_all _ fun p => ?_)
            dsimp only
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
        _ = R k * C := integral_mul_const _ _
    have meas : Continuous (fun y => ∫ p, a k p * (f k).val (y - φ p) ∂ν) := by
      refine continuous_of_dominated (bound := fun p => ‖a k p‖ * C) ?_ ?_
        ((ha k).norm.mul_const C) ?_
      · exact fun y => ((am k).mul ((f k).val.continuous.measurable.comp
          (measurable_const.sub hφ))).aestronglyMeasurable
      · exact fun y => ae_of_all _ fun p => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
      · exact ae_of_all _ fun p => continuous_const.mul
          ((f k).val.continuous.comp (continuous_id.sub continuous_const))
    exact ((kernel (σ (n, s))).integrable.comp_sub_left x).mul_bdd (c := R k * C)
      meas.aestronglyMeasurable (ae_of_all _ inner)
  have blockFormula (x : E) : K g.val x = ∑ k, ∫ p, a k p * K (f k).val (x - φ p) ∂ν := by
    rw [ConeFourierBlocks.block_apply]
    simp_rw [hg, Finset.mul_sum]
    rw [integral_finsetSum _ fun k _ => integrableK k x]
    exact Finset.sum_congr rfl fun k _ =>
      block_family ν (σ (n, s)) (a k) (ha k) (am k) φ hφ (f k).val x
  have leafSupBound (k : ι) : (⨆ c', ∫⁻ x, ‖K (f k).val x‖ₑ ∂family c') ≤
      ENNReal.ofReal (((2 : ℝ) ^ (t s * n))⁻¹ * A0 k) := by
    refine iSup_le fun c' => ?_
    rw [← ofReal_integral_norm_eq_lintegral_enorm
      (SchwartzAmbientRealization.integrable μ leaves _ c')]
    exact ENNReal.ofReal_le_ofReal
      (SchwartzAmbientLeafEntry.leaf_le_core μ hJ leaves (D k) σ t (bD k) (f k) (n, s) c')
  have translated (c : A) (k : ι) (z : E) : (∫⁻ x, ‖K (f k).val (x - z)‖ₑ ∂family c) ≤
      ⨆ c', ∫⁻ x, ‖K (f k).val x‖ₑ ∂family c' := by
    obtain ⟨c', hc'⟩ := translate c (-z)
    have actual := lintegral_map (μ := family c) (f := fun x => ‖K (f k).val x‖ₑ)
      (g := fun x : E => x + -z) (K (f k).val).continuous.measurable.enorm
      (continuous_id.add continuous_const).measurable
    rw [hc'] at actual
    simp only [sub_eq_add_neg]
    rw [← actual]
    exact le_iSup (fun c' => ∫⁻ x, ‖K (f k).val x‖ₑ ∂family c') c'
  have measurableTerm (k : ι) : Measurable (Function.uncurry fun (x : E) (p : P) =>
      ‖a k p‖ₑ * ‖K (f k).val (x - φ p)‖ₑ) :=
    ((am k).comp measurable_snd).enorm.mul ((K (f k).val).continuous.measurable.comp
      (measurable_fst.sub (hφ.comp measurable_snd))).enorm
  have leaf (c : A) : (∫ x, ‖K g.val x‖ ∂family c) ≤ ((2 : ℝ) ^ (t s * n))⁻¹ * Tot := by
    have pointwise (x : E) : ‖K g.val x‖ₑ ≤
        ∑ k, ∫⁻ p, ‖a k p‖ₑ * ‖K (f k).val (x - φ p)‖ₑ ∂ν := by
      rw [blockFormula x]
      refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      exact lintegral_congr fun p => enorm_mul _ _
    have total : (∫⁻ x, ‖K g.val x‖ₑ ∂family c) ≤
        ENNReal.ofReal (((2 : ℝ) ^ (t s * n))⁻¹ * Tot) := by
      calc (∫⁻ x, ‖K g.val x‖ₑ ∂family c)
          ≤ ∫⁻ x, ∑ k, ∫⁻ p, ‖a k p‖ₑ * ‖K (f k).val (x - φ p)‖ₑ ∂ν ∂family c :=
            lintegral_mono pointwise
        _ = ∑ k, ∫⁻ x, ∫⁻ p, ‖a k p‖ₑ * ‖K (f k).val (x - φ p)‖ₑ ∂ν ∂family c :=
            lintegral_finsetSum _ fun k _ => (measurableTerm k).lintegral_prod_right'
        _ = ∑ k, ∫⁻ p, ‖a k p‖ₑ * ∫⁻ x, ‖K (f k).val (x - φ p)‖ₑ ∂family c ∂ν := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [lintegral_lintegral_swap (measurableTerm k).aemeasurable]
            refine lintegral_congr fun p => ?_
            exact lintegral_const_mul _ ((K (f k).val).continuous.measurable.comp
              (measurable_id.sub measurable_const)).enorm
        _ ≤ ∑ k, ∫⁻ p, ‖a k p‖ₑ * ENNReal.ofReal (((2 : ℝ) ^ (t s * n))⁻¹ * A0 k) ∂ν :=
            Finset.sum_le_sum fun k _ => lintegral_mono fun p =>
              mul_le_mul_right ((translated c k (φ p)).trans (leafSupBound k)) _
        _ = ∑ k, ENNReal.ofReal (R k) * ENNReal.ofReal (((2 : ℝ) ^ (t s * n))⁻¹ * A0 k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [lintegral_mul_const _ (am k).enorm, ofReal_integral_norm_eq_lintegral_enorm (ha k)]
        _ = ENNReal.ofReal (((2 : ℝ) ^ (t s * n))⁻¹ * Tot) := by
            rw [hTot, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun k _ =>
              mul_nonneg (inv_nonneg.mpr pow_pos'.le) (mul_nonneg (Rnn k) (A0nn k))]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← ENNReal.ofReal_mul (Rnn k)]
            congr 1
            ring
    rw [← ofReal_integral_norm_eq_lintegral_enorm
      (SchwartzAmbientRealization.integrable μ leaves _ c)] at total
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.mpr pow_pos'.le) Totnn)).mp total
  have blockNorm : ‖SchwartzAmbientBlocks.block μ hJ leaves D' σ (n, s) g‖ ≤
      ((2 : ℝ) ^ (t s * n))⁻¹ * Tot := by
    refine lp.norm_le_of_forall_le (mul_nonneg (inv_nonneg.mpr pow_pos'.le) Totnn) fun c => ?_
    rw [ConeMultiplierBound.block_component_norm]
    exact leaf c
  have weighted : ‖SchwartzAmbientBlocks.weightedBlock μ hJ leaves D' σ t (n, s) g‖ =
      (2 : ℝ) ^ (t s * n) * ‖SchwartzAmbientBlocks.block μ hJ leaves D' σ (n, s) g‖ := by
    change ‖(SchwartzAmbientBlocks.weight t (n, s) •
      SchwartzAmbientBlocks.block μ hJ leaves D' σ (n, s)) g‖ = _
    rw [LinearMap.smul_apply, norm_smul, SchwartzAmbientLeafEntry.weight_norm]
  rw [weighted]
  calc (2 : ℝ) ^ (t s * n) * ‖SchwartzAmbientBlocks.block μ hJ leaves D' σ (n, s) g‖
      ≤ (2 : ℝ) ^ (t s * n) * (((2 : ℝ) ^ (t s * n))⁻¹ * Tot) :=
        mul_le_mul_of_nonneg_left blockNorm pow_pos'.le
    _ = Tot := by rw [← mul_assoc, mul_inv_cancel₀ pow_pos'.ne', one_mul]

/-- Translation does not increase the block core norm. -/
theorem translate_bound [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    {D D' : Set E} (bD : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D σ t)
    (bD' : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D' σ t)
    (f : supportedCore D) (g : supportedCore D') (z : E) (hg : ∀ x, g.val x = f.val (x - z)) :
    ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D' σ t bD' g‖ ≤
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D σ t bD f‖ := by
  have h := family_bound μ hJ leaves σ t translate (ι := Unit) (Measure.dirac ())
    (fun _ _ => (1 : ℂ)) (fun _ => integrable_const _) (fun _ => measurable_const)
    (fun _ => z) measurable_const (fun _ => bD) bD' (fun _ => f) g (fun x => by
      simp only [one_mul, integral_dirac, Finset.univ_unique, Finset.sum_singleton]
      exact hg x)
  simpa only [norm_one, integral_dirac, one_mul, Finset.univ_unique, Finset.sum_singleton]
    using h

/-- A translation difference is bounded by the directional derivative. -/
theorem difference_bound [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    {D D' Dd : Set E}
    (bD' : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D' σ t)
    (bDd : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves Dd σ t)
    (f : supportedCore D) (g : supportedCore D') (d : supportedCore Dd) (z : E)
    (hd : ∀ x, d.val x = fderiv ℝ f.val x z)
    (hg : ∀ x, g.val x = f.val (x - z) - f.val x) :
    ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D' σ t bD' g‖ ≤
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves Dd σ t bDd d‖ := by
  have ftc (x : E) : f.val (x - z) - f.val x = ∫ τ in Ioc (0 : ℝ) 1, -1 * d.val (x - τ • z) := by
    have deriv (τ : ℝ) : HasDerivAt (fun τ : ℝ => f.val (x - τ • z))
        (-1 * d.val (x - τ • z)) τ := by
      have inner : HasDerivAt (fun τ : ℝ => x - τ • z) (-z) τ := by
        simpa only [one_smul, zero_sub, id] using ((hasDerivAt_id τ).smul_const z).const_sub x
      have outer := (f.val.differentiableAt (x := x - τ • z)).hasFDerivAt.comp_hasDerivAt τ inner
      exact outer.congr_deriv (by rw [hd, map_neg, neg_one_mul])
    have cont : Continuous (fun τ : ℝ => -1 * d.val (x - τ • z)) :=
      continuous_const.mul (d.val.continuous.comp (continuous_const.sub
        (continuous_id.smul continuous_const)))
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => deriv τ)
        (cont.intervalIntegrable 0 1)]
    simp only [one_smul, zero_smul, sub_zero]
  have h := family_bound μ hJ leaves σ t translate (ι := Unit) (volume.restrict (Ioc (0 : ℝ) 1))
    (fun _ _ => (-1 : ℂ)) (fun _ => integrable_const _) (fun _ => measurable_const)
    (fun τ => τ • z) (measurable_id.smul_const z) (fun _ => bDd) bD' (fun _ => d) g (fun x => by
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hg x, ftc x])
  have mass : (∫ τ in Ioc (0 : ℝ) 1, ‖(-1 : ℂ)‖) = 1 := by
    simp
  simpa only [Finset.univ_unique, Finset.sum_singleton, mass, one_mul] using h

/-- Mollification converges at rate `ε Σ_k ‖∂_k f‖`. -/
theorem mollifier_bound [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {D D' : Set E} {Dd : ι → Set E}
    (bD' : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D' σ t)
    (bDd : ∀ k, SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves (Dd k) σ t)
    (ρ : E → ℂ) (ρcont : Continuous ρ) (ρint : Integrable ρ) (mass : ∫ y, ρ y = 1)
    (ε : ℝ) (support : ∀ y, ε < ‖y‖ → ρ y = 0)
    (f : supportedCore D) (g : supportedCore D') (d : ∀ k, supportedCore (Dd k))
    (hd : ∀ k x, (d k).val x = fderiv ℝ f.val x (b k))
    (hg : ∀ x, g.val x = (∫ y, ρ y * f.val (x - y)) - f.val x) :
    ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D' σ t bD' g‖ ≤
      ε * (∫ y, ‖ρ y‖) * ∑ k, ‖SchwartzAmbientBlocks.coreMap μ hJ leaves (Dd k) σ t (bDd k) (d k)‖ := by
  let ν : Measure (E × ℝ) := volume.prod (volume.restrict (Ioc (0 : ℝ) 1))
  let a : ι → E × ℝ → ℂ := fun k q => -ρ q.1 * ((inner ℝ (b k) q.1 : ℝ) : ℂ)
  let φ : E × ℝ → E := fun q => q.2 • q.1
  have φm : Measurable φ := measurable_snd.smul measurable_fst
  have am (k : ι) : Measurable (a k) :=
    (ρcont.measurable.comp measurable_fst).neg.mul (Complex.measurable_ofReal.comp
      ((continuous_const.inner continuous_id).measurable.comp measurable_fst))
  have pointBound (k : ι) (y : E) : ‖a k (y, 0)‖ ≤ ε * ‖ρ y‖ := by
    change ‖-ρ y * ((inner ℝ (b k) y : ℝ) : ℂ)‖ ≤ ε * ‖ρ y‖
    by_cases zero : ρ y = 0
    · simp [zero]
    · have near : ‖y‖ ≤ ε := not_lt.mp fun h => zero (support y h)
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc |inner ℝ (b k) y| ≤ ‖b k‖ * ‖y‖ := abs_real_inner_le_norm _ _
        _ = ‖y‖ := by rw [b.orthonormal.1 k, one_mul]
        _ ≤ ε := near
  have aInt (k : ι) : Integrable (a k) ν := by
    have base : Integrable (fun q : E × ℝ => ε * ‖ρ q.1‖) ν :=
      (ρint.norm.const_mul ε).comp_fst (volume.restrict (Ioc (0 : ℝ) 1))
    refine base.mono' (am k).aestronglyMeasurable (ae_of_all _ fun q => ?_)
    exact pointBound k q.1
  obtain ⟨Cd, hCd⟩ : ∃ C : ι → ℝ, ∀ k y, ‖(d k).val y‖ ≤ C k :=
    ⟨fun k => (LeafCommutator.exists_bound (d k).val).choose,
      fun k => (LeafCommutator.exists_bound (d k).val).choose_spec⟩
  have termInt (x : E) (k : ι) : Integrable (fun q => a k q * (d k).val (x - φ q)) ν :=
    (aInt k).mul_bdd (c := Cd k)
      ((d k).val.continuous.measurable.comp (measurable_const.sub φm)).aestronglyMeasurable
      (ae_of_all _ fun q => hCd k _)
  have expand (p y : E) : fderiv ℝ f.val p y = ∑ k, ((inner ℝ (b k) y : ℝ) : ℂ) * (d k).val p := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hd, b.repr_apply_apply, Complex.real_smul]
  have representation (x : E) : g.val x = ∑ k, ∫ q, a k q * (d k).val (x - φ q) ∂ν := by
    obtain ⟨Cf, hCf⟩ := LeafCommutator.exists_bound f.val
    have fint : Integrable (fun y => ρ y * f.val (x - y)) :=
      ρint.mul_bdd (c := Cf) (f.val.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        (ae_of_all _ fun y => hCf _)
    have step1 : g.val x = ∫ y, ρ y * (f.val (x - y) - f.val x) := by
      rw [hg]
      simp_rw [mul_sub]
      rw [integral_sub fint (ρint.mul_const _), integral_mul_const, mass, one_mul]
    rw [← integral_finsetSum _ fun k _ => termInt x k, step1]
    have pointwise (q : E × ℝ) : ∑ k, a k q * (d k).val (x - φ q) =
        -ρ q.1 * fderiv ℝ f.val (x - q.2 • q.1) q.1 := by
      rw [expand, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change -ρ q.1 * ((inner ℝ (b k) q.1 : ℝ) : ℂ) * (d k).val (x - q.2 • q.1) = _
      ring
    have productInt : Integrable (fun q : E × ℝ => -ρ q.1 * fderiv ℝ f.val (x - q.2 • q.1) q.1) ν :=
      (integrable_finsetSum _ fun k _ => termInt x k).congr (ae_of_all _ pointwise)
    rw [integral_congr_ae (ae_of_all _ pointwise), integral_prod _ productInt]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only
    rw [ftc_line f.val x y, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  have h := family_bound μ hJ leaves σ t translate ν a aInt am φ φm bDd bD' d g representation
  have massBound (k : ι) : (∫ q, ‖a k q‖ ∂ν) ≤ ε * ∫ y, ‖ρ y‖ := by
    have mono : (∫ q, ‖a k q‖ ∂ν) ≤ ∫ q, ε * ‖ρ q.1‖ ∂ν :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        ((ρint.norm.const_mul ε).comp_fst (volume.restrict (Ioc (0 : ℝ) 1)))
        (ae_of_all _ fun q => pointBound k q.1)
    refine mono.trans (le_of_eq ?_)
    rw [integral_fun_fst (fun y => ε * ‖ρ y‖), integral_const_mul]
    simp
  calc ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D' σ t bD' g‖
      ≤ ∑ k, (∫ q, ‖a k q‖ ∂ν) * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves (Dd k) σ t (bDd k) (d k)‖ := h
    _ ≤ ∑ k, (ε * ∫ y, ‖ρ y‖) * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves (Dd k) σ t (bDd k) (d k)‖ :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (massBound k) (norm_nonneg _)
    _ = ε * (∫ y, ‖ρ y‖) * ∑ k, ‖SchwartzAmbientBlocks.coreMap μ hJ leaves (Dd k) σ t (bDd k) (d k)‖ := by
        rw [Finset.mul_sum]

/-- The block core norm depends only on the function, not on the support domain. -/
theorem norm_congr {D D' : Set E} (bD : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D σ t)
    (bD' : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D' σ t)
    (f : supportedCore D) (f' : supportedCore D') (h : f.val = f'.val) :
    ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D σ t bD f‖ =
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves D' σ t bD' f'‖ := by
  rw [SchwartzAmbientBlocks.coreMap_norm, SchwartzAmbientBlocks.coreMap_norm]
  congr 1
  funext j
  have same : SchwartzAmbientBlocks.weightedBlock μ hJ leaves D σ t j f =
      SchwartzAmbientBlocks.weightedBlock μ hJ leaves D' σ t j f' := by
    change SchwartzAmbientBlocks.weight t j • SchwartzAmbientRealization.linearMap μ hJ leaves
        (ConeFourierBlocks.block (σ j) f.val) =
      SchwartzAmbientBlocks.weight t j • SchwartzAmbientRealization.linearMap μ hJ leaves
        (ConeFourierBlocks.block (σ j) f'.val)
    rw [h]
  rw [same]

/-- The directional derivative of a compactly supported Schwartz function, as a supported
core element. -/
def derivative (ρ : 𝓢(E, ℂ)) (v : E) : supportedCore (tsupport (ρ : E → ℂ)) :=
  ⟨LineDeriv.lineDerivOp v ρ, fun x hx => by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have zero : fderiv ℝ ρ x = 0 := by
      by_contra hne
      exact hx (support_fderiv_subset ℝ hne)
    rw [zero, zero_apply]⟩

/-- Translations of a compactly supported Schwartz function are Lipschitz in the block norm. -/
theorem translation_lipschitz [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    (bounded : ∀ K : Set E, IsCompact K → SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K σ t)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (ρ : 𝓢(E, ℂ))
    (hρ : HasCompactSupport (ρ : E → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Set E) (bK : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K σ t)
      (h : supportedCore K) (y y' : E), (∀ x, h.val x = ρ (x - y) - ρ (x - y')) →
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t bK h‖ ≤ C * ‖y - y'‖ := by
  set K1 := tsupport (ρ : E → ℂ)
  have bK1 := bounded K1 hρ
  set C := ∑ k, ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t bK1 (derivative ρ (b k))‖
  refine ⟨C, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun K bK h y y' hh => ?_⟩
  set s := y' - y
  -- the translation difference `ρ (· - s) - ρ`
  set K2 := K1 ∪ (fun x => x + s) '' K1
  have K2compact : IsCompact K2 := hρ.union (hρ.image (continuous_id.add continuous_const))
  have bK2 := bounded K2 K2compact
  let g1 : supportedCore K2 := ⟨(SchwartzMap.compSubConstCLM ℝ s ρ) - ρ, fun x hx => by
    have out1 : x ∉ K1 := fun h1 => hx (Or.inl h1)
    have out2 : x - s ∉ K1 := fun h2 => hx (Or.inr ⟨x - s, h2, by simp⟩)
    simp only [sub_apply, SchwartzMap.compSubConstCLM_apply]
    rw [image_eq_zero_of_notMem_tsupport out1, image_eq_zero_of_notMem_tsupport out2, sub_zero]⟩
  have K1sub : K1 ⊆ K2 := subset_union_left
  let rho1 : supportedCore K1 := ⟨ρ, fun x hx => image_eq_zero_of_notMem_tsupport hx⟩
  have ds : supportedCore K1 := derivative ρ s
  have diff := difference_bound μ hJ leaves σ t translate bK2 bK1 rho1 g1 (derivative ρ s) s
    (fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv s ρ x) (fun x => by
      change (SchwartzMap.compSubConstCLM ℝ s ρ - ρ) x = ρ (x - s) - ρ x
      simp [SchwartzMap.compSubConstCLM_apply])
  -- the directional derivative in direction `s` is a combination of basis derivatives
  have expand : derivative ρ s = ∑ k, ((inner ℝ (b k) s : ℝ) : ℂ) • derivative ρ (b k) := by
    apply Subtype.ext
    ext x
    simp only [derivative, Submodule.coe_sum, Submodule.coe_smul, sum_apply,
      smul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    conv_lhs => rw [← b.sum_repr s]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, b.repr_apply_apply, Complex.real_smul, smul_eq_mul]
  have derivBound : ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t bK1 (derivative ρ s)‖ ≤
      C * ‖s‖ := by
    rw [expand, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc |inner ℝ (b k) s| ≤ ‖b k‖ * ‖s‖ := abs_real_inner_le_norm _ _
      _ = ‖s‖ := by rw [b.orthonormal.1 k, one_mul]
  -- `h` is the translate of `-g1` by `y`
  have trans := translate_bound μ hJ leaves σ t translate bK2 bK (-g1) h y (fun x => by
    rw [hh x]
    change ρ (x - y) - ρ (x - y') = -((SchwartzMap.compSubConstCLM ℝ s ρ - ρ) (x - y))
    simp only [sub_apply, SchwartzMap.compSubConstCLM_apply]
    rw [show x - y - s = x - y' by simp only [s]; abel]
    ring)
  rw [map_neg, norm_neg] at trans
  calc ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t bK h‖
      ≤ ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K2 σ t bK2 g1‖ := trans
    _ ≤ ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t bK1 (derivative ρ s)‖ := diff
    _ ≤ C * ‖s‖ := derivBound
    _ = C * ‖y - y'‖ := by rw [← norm_neg, neg_sub]

/-- Cutoffs of translates depend continuously on the translation in the block norm. -/
theorem cutoff_translate_continuous [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    (bounded : ∀ K : Set E, IsCompact K → SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K σ t)
    (a : 𝓢(E, ℂ))
    (multiplier : ∀ (K : Set E) (hK : IsCompact K), ∃ C : ℝ, ∀ f g : supportedCore K,
      g.val = LeafCommutator.mul a f.val →
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K hK) g‖ ≤
        C * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K hK) f‖)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (ρ : 𝓢(E, ℂ))
    (hρ : HasCompactSupport (ρ : E → ℂ))
    {D : Set E} (bD : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D σ t)
    (F : E → supportedCore D) (hF : ∀ y x, (F y).val x = a x * ρ (x - y)) :
    Continuous (fun y => SchwartzAmbientBlocks.coreMap μ hJ leaves D σ t bD (F y)) := by
  obtain ⟨Cl, Cl0, lip⟩ := translation_lipschitz μ hJ leaves σ t translate bounded b ρ hρ
  rw [Metric.continuous_iff]
  intro y0 ε hε
  set K0 := (fun p : E × E => p.1 + p.2) '' (Metric.closedBall y0 1 ×ˢ tsupport (ρ : E → ℂ))
  have K0compact : IsCompact K0 :=
    ((isCompact_closedBall y0 1).prod hρ).image (continuous_fst.add continuous_snd)
  obtain ⟨Cm, mult⟩ := multiplier K0 K0compact
  set Cm' := max Cm 0
  refine ⟨min 1 (ε / (Cm' * Cl + 1)), by positivity, fun y hy => ?_⟩
  have hy1 : dist y y0 < 1 := hy.trans_le (min_le_left _ _)
  have hyε : dist y y0 < ε / (Cm' * Cl + 1) := hy.trans_le (min_le_right _ _)
  have memK0 (z w : E) (hz : dist z y0 ≤ 1) (hw : w ∈ tsupport (ρ : E → ℂ)) : z + w ∈ K0 :=
    ⟨(z, w), ⟨Metric.mem_closedBall.mpr hz, hw⟩, rfl⟩
  have outside (z x : E) (hz : dist z y0 ≤ 1) (hx : x ∉ K0) : ρ (x - z) = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun hmem => hx ?_
    have := memK0 z (x - z) hz hmem
    simpa using this
  let h : supportedCore K0 := ⟨SchwartzMap.compSubConstCLM ℝ y ρ - SchwartzMap.compSubConstCLM ℝ y0 ρ,
    fun x hx => by
      simp only [sub_apply, SchwartzMap.compSubConstCLM_apply]
      rw [outside y x hy1.le hx, outside y0 x (by simp) hx, sub_zero]⟩
  let g : supportedCore K0 := ⟨LeafCommutator.mul a h.val, fun x hx => by
      rw [LeafCommutator.mul_apply, h.property x hx, mul_zero]⟩
  have hb := lip K0 (bounded K0 K0compact) h y y0 (fun x => by
    change (SchwartzMap.compSubConstCLM ℝ y ρ - SchwartzMap.compSubConstCLM ℝ y0 ρ) x = _
    simp only [sub_apply, SchwartzMap.compSubConstCLM_apply])
  have hm := mult h g rfl
  have congr := norm_congr μ hJ leaves σ t bD (bounded K0 K0compact) (F y - F y0) g (by
    ext x
    rw [Submodule.coe_sub, sub_apply, hF, hF]
    change a x * ρ (x - y) - a x * ρ (x - y0) = LeafCommutator.mul a h.val x
    rw [LeafCommutator.mul_apply]
    change _ = a x * (SchwartzMap.compSubConstCLM ℝ y ρ - SchwartzMap.compSubConstCLM ℝ y0 ρ) x
    simp only [sub_apply, SchwartzMap.compSubConstCLM_apply]
    ring)
  rw [dist_eq_norm, ← map_sub, congr]
  calc ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K0 σ t (bounded K0 K0compact) g‖
      ≤ Cm * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K0 σ t (bounded K0 K0compact) h‖ := hm
    _ ≤ Cm' * (Cl * ‖y - y0‖) :=
        mul_le_mul (le_max_left _ _) hb (norm_nonneg _) (le_max_right _ _)
    _ = (Cm' * Cl) * dist y y0 := by rw [dist_eq_norm]; ring
    _ ≤ (Cm' * Cl + 1) * dist y y0 :=
        mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (Cm' * Cl + 1) * (ε / (Cm' * Cl + 1)) :=
        mul_lt_mul_of_pos_left hyε (by positivity)
    _ = ε := by
        have : Cm' * Cl + 1 ≠ 0 := by positivity
        field_simp

/-- Cutoff convolution estimates: with `F = cut · (κ ⋆ G)` and `cut = 1` on the support of
`G`, the norm of `F` is controlled by that of `G`, and `F - G` by `ε`. -/
theorem cutoff_convolution_estimates [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    (bounded : ∀ K : Set E, IsCompact K → SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K σ t)
    (cut : 𝓢(E, ℂ))
    (multiplier : ∀ (K : Set E) (hK : IsCompact K), ∃ C : ℝ, ∀ f g : supportedCore K,
      g.val = LeafCommutator.mul cut f.val →
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K hK) g‖ ≤
        C * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K hK) f‖)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {K : Set E} (Kc : IsCompact K) (G : supportedCore K)
    (one : ∀ x ∈ tsupport (G.val : E → ℂ), cut x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : E → ℂ) (_ : Continuous κ) (_ : Integrable κ)
      (_ : ∫ y, κ y = 1) (ε : ℝ) (_ : ε ≤ 1) (_ : ∀ y, ε < ‖y‖ → κ y = 0)
      (F : supportedCore K) (_ : ∀ x, F.val x = cut x * ∫ y, κ y * G.val (x - y)),
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) F‖ ≤
          C * (∫ y, ‖κ y‖) * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) G‖ ∧
        ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) (F - G)‖ ≤
          C * ε * (∫ y, ‖κ y‖) := by
  set K1 := (fun p : E × E => p.1 + p.2) '' (K ×ˢ Metric.closedBall (0 : E) 1)
  have K1c : IsCompact K1 := (Kc.prod (isCompact_closedBall 0 1)).image
    (continuous_fst.add continuous_snd)
  have KK1 : K ⊆ K1 := fun x hx => ⟨(x, 0), ⟨hx, Metric.mem_closedBall_self zero_le_one⟩, add_zero x⟩
  obtain ⟨Cm, mult⟩ := multiplier K1 K1c
  set Gc := tsupport (G.val : E → ℂ)
  have Gcc : IsCompact Gc :=
    Kc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun x hx => by
      by_contra out; exact hx (G.property x out)) Kc.isClosed)
  set Dsum := ∑ k, ‖SchwartzAmbientBlocks.coreMap μ hJ leaves Gc σ t (bounded Gc Gcc)
    (derivative G.val (b k))‖ with hDsum
  have Dsum0 : 0 ≤ Dsum := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set C := max Cm 0 * (1 + Dsum)
  refine ⟨C, mul_nonneg (le_max_right _ _) (by linarith), ?_⟩
  intro κ κcont κint mass ε εle supp F hF
  have Gcompact : HasCompactSupport (G.val : E → ℂ) := Gcc
  -- the convolution `κ ⋆ G`
  have convSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ y, κ y * G.val (x - y)) :=
    Gcompact.contDiff_convolution_right (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
      κint.locallyIntegrable (G.val.smooth ⊤)
  have convZero (x : E) (hx : x ∉ K1) : ∫ y, κ y * G.val (x - y) = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
    by_cases hy : ε < ‖y‖
    · simp [supp y hy]
    · have hy1 : y ∈ Metric.closedBall (0 : E) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith [not_lt.mp hy]
      have out : x - y ∉ K := fun h => hx ⟨(x - y, y), ⟨h, hy1⟩, sub_add_cancel x y⟩
      simp [G.property _ out]
  have convCompact : HasCompactSupport (fun x => ∫ y, κ y * G.val (x - y)) :=
    HasCompactSupport.intro K1c convZero
  let H : supportedCore K1 := ⟨convCompact.toSchwartzMap convSmooth, convZero⟩
  have Hval (x : E) : H.val x = ∫ y, κ y * G.val (x - y) := rfl
  let G1 : supportedCore K1 := ⟨G.val, fun x hx => G.property x (fun h => hx (KK1 h))⟩
  let F1 : supportedCore K1 := ⟨F.val, fun x hx => F.property x (fun h => hx (KK1 h))⟩
  -- `F = cut · H`
  have FH : F1.val = LeafCommutator.mul cut H.val := by
    ext x
    rw [LeafCommutator.mul_apply, Hval]
    exact hF x
  have bound1 := mult H F1 FH
  have convBound := ConvolutionBlockBound.convolution_bound μ hJ leaves σ t translate (bounded K Kc)
    (bounded K1 K1c) κ κint κcont G H (fun x => Hval x)
  have normF : ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) F‖ =
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t (bounded K1 K1c) F1‖ :=
    norm_congr μ hJ leaves σ t _ _ F F1 rfl
  have κ1 : 0 ≤ ∫ y, ‖κ y‖ := integral_nonneg fun _ => norm_nonneg _
  have NG0 : 0 ≤ ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) G‖ := norm_nonneg _
  constructor
  · rw [normF]
    calc ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t (bounded K1 K1c) F1‖
        ≤ Cm * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t (bounded K1 K1c) H‖ := bound1
      _ ≤ max Cm 0 * ((∫ y, ‖κ y‖) * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) G‖) :=
          mul_le_mul (le_max_left _ _) convBound (norm_nonneg _) (le_max_right _ _)
      _ ≤ C * (∫ y, ‖κ y‖) * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) G‖ := by
          have : max Cm 0 ≤ C := le_mul_of_one_le_right (le_max_right _ _) (by linarith)
          nlinarith [mul_nonneg κ1 NG0]
  · -- `F - G = cut · (H - G)`
    let D1 : supportedCore K1 := H - G1
    let FG : supportedCore K1 := ⟨(F - G).val, fun x hx => (F - G).property x (fun h => hx (KK1 h))⟩
    have FGval : FG.val = LeafCommutator.mul cut D1.val := by
      ext x
      change F.val x - G.val x = LeafCommutator.mul cut (H.val - G.val) x
      rw [LeafCommutator.mul_apply, sub_apply, Hval, hF x, mul_sub]
      congr 1
      by_cases hx : x ∈ Gc
      · rw [one x hx, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    have bound2 := mult D1 FG FGval
    have moll := mollifier_bound μ hJ leaves σ t translate b (bounded K1 K1c) (fun _ => bounded Gc Gcc)
      κ κcont κint mass ε supp G D1 (fun k => derivative G.val (b k))
      (fun k x => SchwartzMap.lineDerivOp_apply_eq_fderiv (b k) G.val x)
      (fun x => by change H.val x - G.val x = _; rw [Hval])
    have normFG : ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) (F - G)‖ =
        ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t (bounded K1 K1c) FG‖ :=
      norm_congr μ hJ leaves σ t _ _ (F - G) FG rfl
    rw [normFG]
    have ε0 : 0 ≤ ε := by
      by_contra neg
      push Not at neg
      have zero : ∀ y, κ y = 0 := fun y => supp y (neg.trans_le (norm_nonneg y))
      simp [zero] at mass
    calc ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t (bounded K1 K1c) FG‖
        ≤ Cm * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t (bounded K1 K1c) D1‖ := bound2
      _ ≤ max Cm 0 * (ε * (∫ y, ‖κ y‖) * Dsum) :=
          mul_le_mul (le_max_left _ _) moll (norm_nonneg _) (le_max_right _ _)
      _ ≤ C * ε * (∫ y, ‖κ y‖) := by
          have h1 : ε * (∫ y, ‖κ y‖) * Dsum ≤ ε * (∫ y, ‖κ y‖) * (1 + Dsum) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg ε0 κ1)
          calc max Cm 0 * (ε * (∫ y, ‖κ y‖) * Dsum)
              ≤ max Cm 0 * (ε * (∫ y, ‖κ y‖) * (1 + Dsum)) :=
                mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
            _ = C * ε * (∫ y, ‖κ y‖) := by ring

/-- The uniform part: `‖cut · (κ ⋆ G)‖ ≤ C ‖κ‖₁ ‖G‖` with `C` depending only on `cut, K`. -/
theorem cutoff_convolution_uniform [∀ c, SFinite ((leaves c).measure μ)]
    (translate : ∀ c (z : E), ∃ c', ((leaves c).measure μ).map (fun x => x + z) =
      (leaves c').measure μ)
    (bounded : ∀ K : Set E, IsCompact K → SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K σ t)
    (cut : 𝓢(E, ℂ))
    (multiplier : ∀ (K : Set E) (hK : IsCompact K), ∃ C : ℝ, ∀ f g : supportedCore K,
      g.val = LeafCommutator.mul cut f.val →
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K hK) g‖ ≤
        C * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K hK) f‖)
    {K : Set E} (Kc : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : supportedCore K) (κ : E → ℂ) (_ : Continuous κ) (_ : Integrable κ)
      (ε : ℝ) (_ : ε ≤ 1) (_ : ∀ y, ε < ‖y‖ → κ y = 0)
      (F : supportedCore K) (_ : ∀ x, F.val x = cut x * ∫ y, κ y * G.val (x - y)),
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) F‖ ≤
          C * (∫ y, ‖κ y‖) * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) G‖ := by
  set K1 := (fun p : E × E => p.1 + p.2) '' (K ×ˢ Metric.closedBall (0 : E) 1)
  have K1c : IsCompact K1 := (Kc.prod (isCompact_closedBall 0 1)).image
    (continuous_fst.add continuous_snd)
  have KK1 : K ⊆ K1 := fun x hx => ⟨(x, 0), ⟨hx, Metric.mem_closedBall_self zero_le_one⟩, add_zero x⟩
  obtain ⟨Cm, mult⟩ := multiplier K1 K1c
  refine ⟨max Cm 0, le_max_right _ _, ?_⟩
  intro G κ κcont κint ε εle supp F hF
  set Gc := tsupport (G.val : E → ℂ)
  have Gcc : IsCompact Gc :=
    Kc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun x hx => by
      by_contra out; exact hx (G.property x out)) Kc.isClosed)
  have Gcompact : HasCompactSupport (G.val : E → ℂ) := Gcc
  have convSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ y, κ y * G.val (x - y)) :=
    Gcompact.contDiff_convolution_right (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
      κint.locallyIntegrable (G.val.smooth ⊤)
  have convZero (x : E) (hx : x ∉ K1) : ∫ y, κ y * G.val (x - y) = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
    by_cases hy : ε < ‖y‖
    · simp [supp y hy]
    · have hy1 : y ∈ Metric.closedBall (0 : E) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith [not_lt.mp hy]
      have out : x - y ∉ K := fun h => hx ⟨(x - y, y), ⟨h, hy1⟩, sub_add_cancel x y⟩
      simp [G.property _ out]
  have convCompact : HasCompactSupport (fun x => ∫ y, κ y * G.val (x - y)) :=
    HasCompactSupport.intro K1c convZero
  let H : supportedCore K1 := ⟨convCompact.toSchwartzMap convSmooth, convZero⟩
  let F1 : supportedCore K1 := ⟨F.val, fun x hx => F.property x (fun h => hx (KK1 h))⟩
  have FH : F1.val = LeafCommutator.mul cut H.val := by
    ext x
    rw [LeafCommutator.mul_apply]
    exact hF x
  have convBound := ConvolutionBlockBound.convolution_bound μ hJ leaves σ t translate (bounded K Kc)
    (bounded K1 K1c) κ κint κcont G H (fun _ => rfl)
  rw [norm_congr μ hJ leaves σ t _ (bounded K1 K1c) F F1 rfl]
  calc ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t (bounded K1 K1c) F1‖
      ≤ Cm * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K1 σ t (bounded K1 K1c) H‖ := mult H F1 FH
    _ ≤ max Cm 0 * ((∫ y, ‖κ y‖) * ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K σ t (bounded K Kc) G‖) :=
        mul_le_mul (le_max_left _ _) convBound (norm_nonneg _) (le_max_right _ _)
    _ = _ := by ring

end Main
end LeanShared.BlockNormCalculus
