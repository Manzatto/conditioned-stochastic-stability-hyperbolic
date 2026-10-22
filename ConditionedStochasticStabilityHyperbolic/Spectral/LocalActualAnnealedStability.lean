module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalKLFamily
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL

/-! The actual finite-block/mixed-norm producers and named classical spectral
contracts construct the two KL applications before producing one local QEM
family, its leading rates, and its zero-noise probability limit. -/

@[expose] public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.LocalActualAnnealedStability
open LeanShared Restriction KellerLiverani1999 KellerLiveraniMeasureStability
open LeanShared.ControlledPlaqueClosure LeanShared.TwoNormNormalization

variable {S H W : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

def outerWeak (i : S →L[ℂ] H) (j : H →L[ℂ] W) : H →L[ℂ] W :=
  (((weakScale (j.comp i))⁻¹ : ℝ) : ℂ) • j

theorem outerWeak_comp (i : S →L[ℂ] H) (j : H →L[ℂ] W) :
    (outerWeak i j).comp i = weakEmbedding (j.comp i) := by
  ext x
  simp only [outerWeak, weakEmbedding, ContinuousLinearMap.comp_apply, smul_apply]
  rfl

theorem outerWeak_injective (i : S →L[ℂ] H) (j : H →L[ℂ] W)
    (hj : Function.Injective j) : Function.Injective (outerWeak i j) := by
  intro x y hxy
  apply hj
  have hc : (((weakScale (j.comp i))⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (weakScale_pos _).ne')
  apply smul_right_injective W hc
  simpa only [outerWeak, smul_apply] using hxy


variable [CompleteSpace S] [CompleteSpace H] [CompleteSpace W]
  {Z Zret Core X Ω : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

set_option maxHeartbeats 800000 in
theorem exists_actual_local_family_from_annealed_sources
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (noise : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (noise ε)]
    (hopen : ∀ ε : ℝ≥0, 0 < ε → (noise ε).IsOpenPosMeasure)
    (F : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (i : S →L[ℂ] H) (j : H →L[ℂ] W)
    (hi : Function.Injective i) (hic : IsCompactOperator i) (hdense : DenseRange i)
    (hj : Function.Injective j) (hjc : IsCompactOperator j)
    (as : ActualAnnealedInputs noise (fun _ε => inferInstance) (j.comp i) R)
    (am : ActualAnnealedInputs noise (fun _ε => inferInstance) j R)
    (essentialS : EssentialRadiusContract (E := S) (W := W))
    (essentialH : EssentialRadiusContract (E := H) (W := W))
    (klS : ClassicalContract (E := S) (W := W))
    (klH : ClassicalContract (E := H) (W := W))
    (ds : DeterministicLeading (as.operator 0)) (dm : DeterministicLeading (am.operator 0))
    (qs δs qm δm : ℝ)
    (hαqs : as.principal / R < qs) (hqs : qs < ds.rate)
    (hqsweak : qs < as.weakRate / R) (hsubqs : ds.subordinate < qs)
    (hδs : 0 < δs) (hδssub : δs < qs - ds.subordinate) (hδslead : δs < ds.rate - qs)
    (hαqm : am.principal / R < qm) (hqmrate : qm < dm.rate)
    (hqmweak : qm < am.weakRate / R) (hsubqm : dm.subordinate < qm)
    (hδm : 0 < δm) (hδmsub : δm < qm - dm.subordinate) (hδmlead : δm < dm.rate - qm)
    (hqm : 0 < qm)
    (φ : W →L[ℂ] ℂ) (hφ : φ ((outerWeak i j) (i ds.vector)) ≠ 0)
    (A : Set (K →ᵇ ℝ)) (hA : Dense A) (M : A → H →L[ℂ] H) (ν₀ : ProbabilityMeasure K)
    (projectorComparison :
      ∀ os : ProjectorOutputs as.operator ((outerWeak i j).comp i) ds qs δs,
      ∀ om : ProjectorOutputs am.operator (weakEmbedding j) dm qm δm,
      ∀ ε ≤ min os.window om.window, (om.projection ε).comp i = i.comp (os.projection ε))
    (physicalSources :
      ∀ om : ProjectorOutputs am.operator (weakEmbedding j) dm qm δm,
      ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
        Nonempty (LocalKLFamily.ScaleSources (Z := Z) (Zret := Zret) (Core := Core)
          T V K G hK (noise ε) (F ε) (hF ε) w hw wc hwc R hR hwR hwcR om ε η A M))
    (equilibriumIdentification :
      ∀ os : ProjectorOutputs as.operator ((outerWeak i j).comp i) ds qs δs,
      ∀ om : ProjectorOutputs am.operator (weakEmbedding j) dm qm δm,
      ∀ h : A, (∫ x, h.val x ∂(ν₀ : Measure K)) =
        realLeftTrace os om φ 0 (M h (i ds.vector))) :
    ∃ (ν : ℝ≥0 → ProbabilityMeasure K) (r : ℝ≥0 → ℝ),
      Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) ∧
      Tendsto r (𝓝[>] (0 : ℝ≥0)) (𝓝 (R * dm.rate)) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
        let C := RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet
          w hw.measurable R hR hwR
        C.IsQuasiErgodic (ν ε : Measure K) ∧
        (ν ε : Measure K).support ⊆ retainedRegion K U ∧
        {x : K | x.val ∈ isolatedCore T K} ⊆ (ν ε : Measure K).support ∧
        (∀ ζ : Measure K, C.IsQuasiErgodic ζ →
          {x : K | x.val ∈ isolatedCore T K} ⊆ ζ.support → ζ = (ν ε : Measure K)) ∧
        0 < r ε ∧ ∃ hSF : HasStrongFellerKernel C,
          spectralRadius ℝ (R • strongFellerTransferOperator C hSF) = ENNReal.ofReal (r ε) := by
  obtain ⟨os'⟩ := as.exists_projector_outputs essentialS klS
    (hj.comp hi) (hic.clm_comp j) ds qs δs hαqs hqs hqsweak hsubqs hδs hδssub hδslead
  have houter := outerWeak_comp i j
  rw [← houter] at os'
  let os := os'
  obtain ⟨om⟩ := am.exists_projector_outputs essentialH klH hj hjc dm qm δm
    hαqm hqmrate hqmweak hsubqm hδm hδmsub hδmlead
  obtain ⟨ν, hνlim, hν⟩ := LocalKLFamily.exists_actual_local_qem_family_with_weak_limit
    T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore noise hopen F hF
    w hw hwG wc hwc R hR hwR hwcR os om hδmsub hδmlead hqm hic
    (outerWeak_injective i j hj) hdense (projectorComparison os om) φ hφ A hA M ν₀
    (physicalSources om) (equilibriumIdentification os om)
  let r : ℝ≥0 → ℝ := fun ε => R * (om.eigenvalue ε).re
  have hrlim : Tendsto r (𝓝[>] (0 : ℝ≥0)) (𝓝 (R * dm.rate)) := by
    have he : Tendsto (fun ε => (om.eigenvalue ε).re) (𝓝 0) (𝓝 dm.rate) :=
      Complex.continuous_re.continuousAt.tendsto.comp om.eigenvalue_convergence
    exact ((tendsto_const_nhds (x := R)).mul he).mono_left nhdsWithin_le_nhds
  refine ⟨ν, r, hνlim, hrlim, ?_⟩
  filter_upwards [hν, physicalSources om 1 zero_lt_one] with ε hq hs
  obtain ⟨s⟩ := hs
  let so := s.sameCutoff.originalInputs om hδmsub hδmlead hqm ε
    (RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet wc hwc R hR hwcR)
    (RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet w hw.measurable R hR hwR)
    s.cutoffSF s.originalSF R hR
  obtain ⟨d, hr, _⟩ := so.exists_gap
  have hr' : d.rate = r ε := hr
  exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2,
    hr' ▸ d.rate_pos, s.originalSF, by rw [d.spectralRadius_eq_rate, hr']⟩

end ConditionedStochasticStabilityHyperbolic.LocalActualAnnealedStability
