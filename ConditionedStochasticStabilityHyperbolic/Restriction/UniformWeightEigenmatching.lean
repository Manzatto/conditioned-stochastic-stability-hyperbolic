module

public import ConditionedStochasticStabilityHyperbolic.Restriction.UniformNoiseLocalization
public import ConditionedStochasticStabilityHyperbolic.Restriction.WeightAgreement

/-! Uniform original-to-cutoff eigenvector matching from actual no-return
and finite extinction. Neither mixing nor analytic projectors enter. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped BoundedContinuousFunction Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Restriction
open LeanShared
variable {X Ω : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem exists_uniform_raw_weight_eigenmatching
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) [CompactSpace K]
    (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U) :
    ∃ η : ℝ, 0 < η ∧ ∀ (ρ : Measure Ω) [IsProbabilityMeasure ρ]
      (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ z, dist (F (x, z)) (T x) < η) →
      ∀ (w wc : K → ℝ) (hw : Measurable w) (hwc : Measurable wc)
      (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R),
      (∀ x : K, x.val ∈ closure U → w x = wc x) →
      let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw R hR hwR
      let D := RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc R hR hwcR
      ∀ (sf : HasStrongFellerKernel C) (sfd : HasStrongFellerKernel D)
      (f : K →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ, z ≠ 0 →
        (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf) f = z • f →
        ∃ g : K →ᵇ ℂ, g ≠ 0 ∧
          (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) D sfd) g = z • g := by
  obtain ⟨r₀, hr₀, hnonreturn⟩ := exists_uniform_nonreturn T.continuous
    isClosed_closure.isCompact (isClosed_forwardTrapped T.continuous hK.isClosed) hU hsep
  let S := Metric.thickening r₀ (forwardTrapped T K)
  obtain ⟨N, _, η, hη, hcert⟩ := UniformNoiseLocalization.exists_uniform_geometric_lifting_certificates
    (Ω := Ω) T K U S hK hU Metric.isOpen_thickening hcore
      (Metric.self_subset_thickening hr₀ _)
  refine ⟨min η r₀, lt_min hη hr₀, ?_⟩
  intro ρ _ F hF hclose w wc hw hwc R hR hwR hwcR heq
  dsimp only
  intro sf sfd f hf z hz he
  have hnear : ∀ x ∈ K, ∀ a, dist (F (x, a)) (T x) < η :=
    fun x hx a => (hclose x hx a).trans_le (min_le_left _ _)
  have hno : ∀ x ∈ K, x ∈ closure U → ∀ a, F (x, a) ∉ S \ U := by
    intro x _hx hx a
    exact hnonreturn (fun y => F (y, a))
      (fun y hy => (hclose y (hUK hy) a).trans_le (min_le_right _ _)) x hx
  obtain ⟨hrC, heC, hcC⟩ := hcert ρ w hw R hR hwR F hF hnear hno
  obtain ⟨hrD, heD, hcD⟩ := hcert ρ wc hwc R hR hwcR F hF hnear hno
  let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw R hR hwR
  let D := RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc R hR hwcR
  let V := retainedRegion K U
  have hV : MeasurableSet V := isClosed_closure.measurableSet.preimage measurable_subtype_coe
  have hkernel := restricted_weighted_kernel_eq ρ F hF K hK.measurableSet V hV
    w wc hw hwc R hR hwR hwcR heq
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hnorm : ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf f = (z / R) • f := by
    have hr : (R : ℂ) • (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf f) = z • f := by
      simpa only [smul_apply, Complex.coe_smul] using he
    have hs := congrArg (fun v : K →ᵇ ℂ => (R : ℂ)⁻¹ • v) hr
    simpa only [smul_smul, inv_mul_cancel₀ hRc, one_smul, div_eq_mul_inv, mul_comm] using hs
  have hgen : ((ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf - (z / R) • 1) ^ (1 : ℕ)) f = 0 := by
    simpa only [pow_one, sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] using hnorm
  obtain ⟨g, hg, _, hge⟩ := exists_matching_nonzero_generalized_eigenfunction
    C D sf sfd V (badRegion K S) (badRegion K S) hV hkernel hrC heC hrD heD
    N N hcC hcD (div_ne_zero hz hRc) 1 f hf hgen
  refine ⟨g, hg, ?_⟩
  have hng : ComplexStrongFeller.transferOperator (𝕜 := ℂ) D sfd g = (z / R) • g := by
    simpa only [pow_one, sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] using hge
  have hs := congrArg (fun v : K →ᵇ ℂ => (R : ℂ) • v) hng
  simpa only [smul_apply, Complex.coe_smul, smul_smul, div_eq_mul_inv,
    mul_left_comm (R : ℂ) z, mul_inv_cancel₀ hRc, mul_one] using hs


/-- The actual law-varying original process inherits individual spectral
comparison from its analytic cutoff, with one geometric tolerance. -/
theorem exists_uniform_original_eigencomparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) [CompactSpace K]
    (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U) :
    ∃ η : ℝ, 0 < η ∧ ∀ (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
      (F : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
      (w wc : K → ℝ) (hw : Measurable w) (hwc : Measurable wc)
      (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R),
      (∀ x : K, x.val ∈ closure U → w x = wc x) →
      ∀ (P : ℝ≥0 → E →L[ℂ] E) (α : ℝ≥0 → ℝ), (∀ ε, 0 ≤ α ε) →
      (∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x ∈ K, ∀ z, dist (F ε (x, z)) (T x) < η) →
      (∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F ε) (hF ε) K hK.measurableSet wc hwc R hR hwcR)) →
      (∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ sf : HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F ε) (hF ε) K hK.measurableSet wc hwc R hR hwcR),
        ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
          (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) _ sf) f = z • f →
          α ε < ‖z‖ → z ∈ spectrum ℂ (P ε)) →
      ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ sf : HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F ε) (hF ε) K hK.measurableSet w hw R hR hwR),
        ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
          (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) _ sf) f = z • f →
          α ε < ‖z‖ → z ∈ spectrum ℂ (P ε) := by
  obtain ⟨η, hη, matching⟩ := exists_uniform_raw_weight_eigenmatching (Ω := Ω) T K U hK hU hcore hUK hsep
  refine ⟨η, hη, ?_⟩
  intro ρ _ F hF w wc hw hwc R hR hwR hwcR heq P α hα close sfCut comparison
  filter_upwards [close, sfCut, comparison] with ε hclose sfd hc
  intro sf f hf z he hz
  have hz0 : z ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hz
    exact (not_lt_of_ge (hα ε)) hz
  obtain ⟨g, hg, hge⟩ := matching (ρ ε) (F ε) (hF ε) hclose w wc hw hwc R hR hwR hwcR heq
    sf sfd f hf z hz0 he
  exact hc sfd g hg z hge hz

end ConditionedStochasticStabilityHyperbolic.Restriction
