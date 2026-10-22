module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComparedNoiseQEM
public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.InverseDensityPositivity

/-! # Local process conclusions from the compared anisotropic spectrum

The raw manuscript operator supplies a simple dominant analytic eigenvalue
and real-compatible leading data through the classical spectral comparison.
The continuous-space remainder radius, real power gap, leading measure,
quasi-ergodicity, core positivity, geometric localization and qualified
uniqueness are conclusions. Actual manifold and spectral-comparison producers
remain explicit. Inverse-density positivity is needed to establish that the
constructed measure itself contains the entire core in its support.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.ComparedLocalQuasiErgodic

open LeanShared LocalPositiveEigenfunction Restriction
open LeanShared.ControlledPlaqueClosure

variable {X Ω A W : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The local geometric tolerance works uniformly for all noise maps whose
compared analytic spectrum has the stated leading data. A raw continuous
rank-one gap is constructed internally. -/
theorem exists_noise_tolerance_for_compared_local_package
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (noise : Measure Ω) [IsProbabilityMeasure noise] [noise.IsOpenPosMeasure]
    (w : K → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ForwardPlaqueInputs T F V K G →
      ∀ (hSF : RestrictedStrongFeller.HasStrongFellerNoise noise F hF),
      let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
      let Q := (R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C
        (RestrictedStrongFeller.hasStrongFeller_chain noise F hF K hK.measurableSet
          w hw (fun x => (hwpos x).le) R hR hwR hSF)
      let P := RestrictedStrongFeller.rawTransferOperator noise F hF K hK.measurableSet
        w hw (fun x => (hwpos x).le) R hR hwR hSF
      ∀ (Panalytic : A →L[ℂ] A) (a : A →L[ℂ] W) (b : (K →ᵇ ℂ) →L[ℂ] W),
      Function.Injective b → ∀ ρ r : ℝ, ρ < r → 0 < r →
      PowerCompactGap.SquareCompactFredholm (F := K →ᵇ ℂ) →
      IsCompactOperator (Q ^ 2 : (K →ᵇ ℂ) →L[ℂ] (K →ᵇ ℂ)) →
      ComparedSpectralGap.EigenvectorComparison Panalytic Q a b ρ →
      ∀ (γ : A) (g : K →ᵇ ℝ) (μ : (K →ᵇ ℝ) →L[ℝ] ℝ) (ℓ : (K →ᵇ ℂ) →L[ℂ] ℂ),
      b (AbsorbingMarkovChains.ComplexKernel.ofReal g) = a γ →
      (∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ)) →
      μ g = 1 → 0 < μ 1 →
      Q (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
        (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g →
      (∀ f, ℓ (Q f) = (r : ℂ) * ℓ f) →
      (∀ v : A, v ≠ 0 → ∀ z : ℂ, Panalytic v = z • v → ‖z‖ ≤ r) →
      (∀ v : A, v ≠ 0 → ∀ z : ℂ,
        Panalytic v = z • v → ‖z‖ = r → z = (r : ℂ)) →
      (∀ v : A, Panalytic v = (r : ℂ) • v → ∃ c : ℂ, v = c • γ) →
      ∃ ν : Measure K, IsFiniteMeasure ν ∧
        (∀ f : K →ᵇ ℝ, μ f = ∫ y, f y ∂ν) ∧
        C.IsQuasiErgodic (eigenvectorMeasure ν g) ∧
        (eigenvectorMeasure ν g).support ⊆ retainedRegion K U ∧
        (∀ x : K, x.val ∈ isolatedCore T K → 0 < g x) ∧
        (∀ η : Measure K, C.IsQuasiErgodic η →
          {x : K | x.val ∈ isolatedCore T K} ⊆ η.support → η = eigenvectorMeasure ν g) ∧
        (∀ v : K →ᵇ ℝ, P v = r • v → v = μ v • g) ∧
        spectralRadius ℝ P = ENNReal.ofReal r := by
  obtain ⟨δ, hδ, hpackage⟩ := LocalQuasiErgodic.exists_noise_tolerance_for_local_package
    T V K G U hV hVK hK hG hU hcoreU hUV hsep hcoreG htrans hcore noise
    w hw hwpos R hR hwR
  refine ⟨δ, hδ, ?_⟩
  intro F hF hclose hp hSF
  dsimp only
  intro Panalytic a b hb ρ r hρr hr hFredholm hcompact hcompare γ g μ ℓ
    hident hreal hpair hmass hright hleft hbound hperipheral hsimple
  let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
  let hSFk := RestrictedStrongFeller.hasStrongFeller_chain noise F hF K hK.measurableSet
    w hw (fun x => (hwpos x).le) R hR hwR hSF
  let Q := (R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSFk
  have hpairC : ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal g) = 1 := by
    rw [hreal, hpair]
    rfl
  have hgC : AbsorbingMarkovChains.ComplexKernel.ofReal g ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hpairC
    exact zero_ne_one hpairC
  let : Nontrivial (K →ᵇ ℂ) := ⟨⟨AbsorbingMarkovChains.ComplexKernel.ofReal g, 0, hgC⟩⟩
  have hspec := ComparedSpectralGap.complementary_radius_lt Panalytic Q a b ρ r hρr hcompare
    hFredholm hcompact hb hr γ (AbsorbingMarkovChains.ComplexKernel.ofReal g)
    hident ℓ hpairC hright hleft hbound hperipheral hsimple
  obtain ⟨d, hdr, hdμ, hdg⟩ := NoiseSpectralGap.exists_rawRankOne C hSFk R r hr g μ ℓ
    hreal hpair hmass hright hleft hspec
  have hdtype : R • strongFellerTransferOperator C hSFk =
      RestrictedStrongFeller.rawTransferOperator noise F hF K hK.measurableSet
        w hw (fun x => (hwpos x).le) R hR hwR hSF := rfl
  let d' := hdtype ▸ d
  obtain ⟨ν, hν, hm, hq, hlocal, hgpos, hunique, hsimpleR⟩ :=
    hpackage F hF hclose hp hSF d'
  have hdr' : d'.rate = r := hdr
  have hdμ' : d'.mean = μ := hdμ
  have hdg' : d'.eigenvector = g := hdg
  refine ⟨ν, hν, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hdμ'] using hm
  · simpa only [hdg'] using hq
  · simpa only [hdg'] using hlocal
  · simpa only [hdg'] using hgpos
  · simpa only [hdg'] using hunique
  · simpa only [hdr', hdμ', hdg'] using hsimpleR
  · rw [← hdr']
    exact d'.spectralRadius_eq_rate

omit [CompactSpace X] [SecondCountableTopology X] in
/-- Support of a subtype pushforward reflects support on the subtype. -/
theorem mem_support_of_mem_support_map (K : Set X) (ν : Measure K) (x : K)
    (hx : x.val ∈ (ν.map Subtype.val).support) : x ∈ ν.support := by
  rw [Measure.support_eq_forall_isOpen]
  intro B hxB hB
  obtain ⟨O, hO, hOB⟩ := isOpen_induced_iff.mp hB
  have hxO : x.val ∈ O := by rw [← hOB] at hxB; exact hxB
  have hpos := (Measure.mem_support_iff_forall x.val).mp hx O (hO.mem_nhds hxO)
  rwa [Measure.map_apply measurable_subtype_coe hO.measurableSet, hOB] at hpos

omit [CompactSpace X] in
/-- The forward density product localized in the retained subtype region is
localized in the prescribed ambient interior as well. -/
theorem ambient_product_localization
    (K U V : Set X) (hUV : closure U ⊆ V)
    (ν : Measure K) [IsFiniteMeasure ν] (g : K →ᵇ ℝ)
    (hlocal : (eigenvectorMeasure ν g).support ⊆ retainedRegion K U) :
    ((eigenvectorMeasure ν g).map Subtype.val).support ⊆ V := by
  have hconull : retainedRegion K U ∈ ae (eigenvectorMeasure ν g) := by
    exact Filter.mem_of_superset Measure.support_mem_ae hlocal
  have hz : (eigenvectorMeasure ν g) (retainedRegion K U)ᶜ = 0 := by
    simpa only [mem_ae_iff] using hconull
  have hamb : ((eigenvectorMeasure ν g).map Subtype.val).support ⊆ closure U := by
    apply Measure.support_subset_of_isClosed isClosed_closure
    change ((eigenvectorMeasure ν g).map Subtype.val) (closure U)ᶜ = 0
    rw [Measure.map_apply measurable_subtype_coe isClosed_closure.measurableSet.compl]
    exact hz
  exact hamb.trans hUV

/-- The inverse density producer yields support on the literal live subtype. Forward and inverse
eigenrelations, normalization, localization and nonnegativity are derived from the actual
normalized gap and representation. The density identification and inverse weighted-kernel
duality are the remaining classical geometric/regularity inputs. -/
theorem exists_noise_tolerance_for_inverse_support_from_actual_data
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) (hUV : closure U ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (noise : Measure Ω) [IsProbabilityMeasure noise] [noise.IsOpenPosMeasure]
      (F : X × Ω → X) (hF : Measurable F) (w : K → ℝ) (hw : Measurable w)
      (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R),
      let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw R hR hwR
      let J := LeanShared.WeightedConditioning.normalizedKernel
        (LeanShared.RandomMapKernel.killed noise F hF K hK.measurableSet)
        (SubtypeKernel.zeroExtend K w) R
        (SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hw)
      ∀ (hSF : HasStrongFellerKernel C)
        (d : RankOneSpectralData (strongFellerTransferOperator C hSF) (1 : K →ᵇ ℝ))
        (ν : Measure K) [IsFiniteMeasure ν],
      (∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂ν) →
      (eigenvectorMeasure ν d.eigenvector).support ⊆ retainedRegion K U →
      (∀ x : K, x.val ∈ isolatedCore T K → 0 < d.eigenvector x) →
      ∀ (H : X × Ω → X) (_hH : Measurable H),
      (∀ x ∈ K, ∀ ω, dist (H (x, ω)) (T.symm x) < δ) →
      ForwardPlaqueInputs T.symm H V K G →
      ∀ (Wnoise : X × Ω → ℝ) (_hWnoise : Measurable Wnoise) (B : ℝ),
      (∀ x ∈ K, ∀ ω, Wnoise (x, ω) ≤ B) →
      (∀ x ∈ K, ∀ ω, 0 < Wnoise (x, ω)) →
      let L := LeanShared.WeightedRandomMapKernel.killed noise Wnoise H K hK.measurableSet
      ∀ (σ : Measure X) [IsFiniteMeasure σ] (m : X → ℝ),
      σ.support = K → Measurable m → (∀ x, 0 ≤ m x) → ContinuousOn m K →
      ν.map Subtype.val = eigenvectorMeasure σ m →
      LeanShared.KernelAdjointDensity.IsAdjoint J L σ →
      ContinuousOn (fun x => ∫ y, m y ∂L x) K →
      {x : K | x.val ∈ isolatedCore T K} ⊆ (eigenvectorMeasure ν d.eigenvector).support := by
  obtain ⟨δ, hδ, hcert⟩ := InverseDensityPositivity.exists_noise_tolerance_for_core_subset_product_support
    (Ω := Ω) T V K G hV hVK hK hG hcoreV hcoreG htrans
  refine ⟨δ, hδ, ?_⟩
  intro noise _ _ F hF w hw R hR hwR
  dsimp only
  intro hSF d ν _ hm hlocal hgpos H hH hclose hp Wnoise hWnoise B hB hWpos
    σ _ m hσ hmMeas hm0 hmc hrepr hdual hLmc
  let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw R hR hwR
  let J := LeanShared.WeightedConditioning.normalizedKernel
    (LeanShared.RandomMapKernel.killed noise F hF K hK.measurableSet)
    (SubtypeKernel.zeroExtend K w) R
    (SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hw)
  let : IsFiniteKernel J := LeanShared.WeightedConditioning.normalizedKernel_isFinite
    _ _ R _ hR (SubtypeKernel.zeroExtend_le K w R hR.le hwR)
    (LeanShared.RandomMapKernel.killed_mass_le_one noise F hF K hK.measurableSet)
  let : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let g := SubtypeKernel.zeroExtend K d.eigenvector
  have hgMeas : Measurable g :=
    SubtypeKernel.measurable_zeroExtend K hK.measurableSet _ d.eigenvector.continuous.measurable
  have hg0K : ∀ x : K, 0 ≤ d.eigenvector x :=
    d.eigenvector_nonneg_of_positive (representedTransfer_positive C.killedTransition
      (strongFellerTransferOperator C hSF) (strongFellerTransferOperator_represents C hSF))
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ K
    · rw [show g x = d.eigenvector ⟨x, hx⟩ from SubtypeKernel.zeroExtend_coe K _ ⟨x, hx⟩]
      exact hg0K ⟨x, hx⟩
    · rw [show g x = 0 from SubtypeKernel.zeroExtend_of_not_mem K _ x hx]
  have hgcont : ContinuousOn g K := continuousOn_zeroExtend K d.eigenvector
  have hrightK (x : K) : ∫ y, d.eigenvector y ∂C.killedTransition x =
      d.rate * d.eigenvector x := by
    rw [← strongFellerTransferOperator_represents C hSF]
    simpa only [BoundedContinuousFunction.smul_apply, smul_eq_mul] using
      congrArg (fun f : K →ᵇ ℝ => f x) d.right_eigenvector
  have hright : ∀ x ∈ K, ∫ y, g y ∂J x = d.rate * g x := by
    intro x hx
    change ∫ y, SubtypeKernel.zeroExtend K d.eigenvector y ∂J x =
      d.rate * SubtypeKernel.zeroExtend K d.eigenvector x
    rw [SubtypeKernel.zeroExtend_coe K d.eigenvector ⟨x, hx⟩]
    exact ambient_right_law noise F hF K hK.measurableSet w hw R hR hwR
        d.eigenvector d.rate hrightK ⟨x, hx⟩
  have hleftK := rankOne_left_eigenmeasure d C.killedTransition
    (strongFellerTransferOperator_represents C hSF) ν hm
  have hleft : J ∘ₘ eigenvectorMeasure σ m = ENNReal.ofReal d.rate • eigenvectorMeasure σ m := by
    rw [← hrepr]
    exact map_left_eigenmeasure C.killedTransition J Subtype.val measurable_subtype_coe
      (map_live_killedTransition noise F hF K hK.measurableSet w hw R hR hwR) ν _ hleftK
  have hnorm : ∫ x, g x ∂eigenvectorMeasure σ m = 1 := by
    rw [← hrepr, integral_zeroExtend_map K hK.measurableSet, ← hm, d.mean_eigenvector]
  have hproduct : eigenvectorMeasure (eigenvectorMeasure σ m) g =
      (eigenvectorMeasure ν d.eigenvector).map Subtype.val := by
    rw [← hrepr]
    exact (map_eigenvectorMeasure_zeroExtend K hK.measurableSet ν d.eigenvector
      d.eigenvector.continuous.measurable).symm
  have hlocalAmbient : (eigenvectorMeasure (eigenvectorMeasure σ m) g).support ⊆ V := by
    rw [hproduct]
    exact ambient_product_localization K U V hUV ν d.eigenvector hlocal
  have hJtarget : ∀ x ∈ K, (J x).restrict K = J x := by
    intro x _
    change (ENNReal.ofReal (SubtypeKernel.zeroExtend K w x / R) •
      ((LeanShared.RandomMapKernel.transition noise F hF x).restrict K)).restrict K = _
    rw [Measure.restrict_smul, Measure.restrict_restrict hK.measurableSet, inter_self]
    rfl
  have hcorepos : ∀ x ∈ isolatedCore T K, 0 < g x := by
    intro x hx
    have hxK : x ∈ K := forwardTrapped_subset T K hx.1
    rw [show g x = d.eigenvector ⟨x, hxK⟩ from SubtypeKernel.zeroExtend_coe K _ ⟨x, hxK⟩]
    exact hgpos ⟨x, hxK⟩ hx
  have hsupp := hcert noise H hH hclose hp Wnoise hWnoise B hB hWpos
    J σ hσ hJtarget hdual g m hgMeas hmMeas hg0 hm0 hgcont hmc hLmc d.rate d.rate_pos
    hleft hright hnorm hlocalAmbient hcorepos
  intro x hx
  apply mem_support_of_mem_support_map K _ x
  rw [← hproduct]
  exact hsupp hx

/-- Precise raw spectral-comparison outputs. No real geometric gap or
complementary radius, measure, positivity or support conclusion is a field. -/
structure ComparedRawSpectralInputs {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (C : AbsorbingMarkovChains.CanonicalChain Y)
    (hSF : HasStrongFellerKernel C) (R : ℝ) where
  analyticOperator : A →L[ℂ] A
  analyticEmbedding : A →L[ℂ] W
  continuousEmbedding : (Y →ᵇ ℂ) →L[ℂ] W
  embedding_injective : Function.Injective continuousEmbedding
  cutoff : ℝ
  rate : ℝ
  cutoff_lt_rate : cutoff < rate
  rate_pos : 0 < rate
  fredholm : PowerCompactGap.SquareCompactFredholm (F := Y →ᵇ ℂ)
  square_compact : IsCompactOperator
    (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) ^ 2 :
      (Y →ᵇ ℂ) →L[ℂ] (Y →ᵇ ℂ))
  comparison : ComparedSpectralGap.EigenvectorComparison analyticOperator
    ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
    analyticEmbedding continuousEmbedding cutoff
  analyticVector : A
  eigenvector : Y →ᵇ ℝ
  mean : (Y →ᵇ ℝ) →L[ℝ] ℝ
  complexMean : (Y →ᵇ ℂ) →L[ℂ] ℂ
  vector_identification : continuousEmbedding
    (AbsorbingMarkovChains.ComplexKernel.ofReal eigenvector) = analyticEmbedding analyticVector
  real_compatibility : ∀ f, complexMean (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (mean f : ℂ)
  normalization : mean eigenvector = 1
  mean_one_pos : 0 < mean 1
  right_equation : ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
    (AbsorbingMarkovChains.ComplexKernel.ofReal eigenvector) =
    (rate : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal eigenvector
  left_equation : ∀ f, complexMean
    (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) f) =
      (rate : ℂ) * complexMean f
  eigenvalue_bound : ∀ v : A, v ≠ 0 → ∀ z : ℂ,
    analyticOperator v = z • v → ‖z‖ ≤ rate
  peripheral_exclusion : ∀ v : A, v ≠ 0 → ∀ z : ℂ,
    analyticOperator v = z • v → ‖z‖ = rate → z = (rate : ℂ)
  leading_simple : ∀ v : A, analyticOperator v = (rate : ℂ) • v →
    ∃ c : ℂ, v = c • analyticVector

/-- The structure's spectral outputs construct the raw real gap. -/
theorem ComparedRawSpectralInputs.exists_rawRankOne
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    {C : AbsorbingMarkovChains.CanonicalChain Y} {hSF : HasStrongFellerKernel C} {R : ℝ}
    (s : ComparedRawSpectralInputs (A := A) (W := W) C hSF R) :
    ∃ d : RankOneSpectralData (R • strongFellerTransferOperator C hSF) (1 : Y →ᵇ ℝ),
      d.rate = s.rate ∧ d.mean = s.mean ∧ d.eigenvector = s.eigenvector := by
  have hpairC : s.complexMean (AbsorbingMarkovChains.ComplexKernel.ofReal s.eigenvector) = 1 := by
    rw [s.real_compatibility, s.normalization]
    rfl
  have hgC : AbsorbingMarkovChains.ComplexKernel.ofReal s.eigenvector ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hpairC
    exact zero_ne_one hpairC
  let : Nontrivial (Y →ᵇ ℂ) := ⟨⟨AbsorbingMarkovChains.ComplexKernel.ofReal s.eigenvector, 0, hgC⟩⟩
  have hspec := ComparedSpectralGap.complementary_radius_lt s.analyticOperator
    ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
    s.analyticEmbedding s.continuousEmbedding s.cutoff s.rate s.cutoff_lt_rate s.comparison
    s.fredholm s.square_compact s.embedding_injective s.rate_pos s.analyticVector
    (AbsorbingMarkovChains.ComplexKernel.ofReal s.eigenvector) s.vector_identification
    s.complexMean hpairC s.right_equation s.left_equation s.eigenvalue_bound
    s.peripheral_exclusion s.leading_simple
  exact NoiseSpectralGap.exists_rawRankOne C hSF R s.rate s.rate_pos s.eigenvector s.mean
    s.complexMean s.real_compatibility s.normalization s.mean_one_pos s.right_equation
    s.left_equation hspec

/-- Physical inverse and density inputs. They retain the state-and-noise
weight in the Jacobian duality and specify actual measure equality. There is
no eigenrelation, normalization, localization, support or density positivity
on the isolated core among these fields. -/
structure InverseDensityInputs
    (T : X ≃ₜ X) (V K G : Set X) (hK : IsCompact K)
    (noise : Measure Ω) [IsProbabilityMeasure noise]
    (F : X × Ω → X) (hF : Measurable F)
    (w : K → ℝ) (hw : Measurable w) (R : ℝ)
    (ν : Measure K) (δ : ℝ) where
  inverseMap : X × Ω → X
  inverse_measurable : Measurable inverseMap
  inverse_close : ∀ x ∈ K, ∀ ω, dist (inverseMap (x, ω)) (T.symm x) < δ
  inverse_plaques : ForwardPlaqueInputs T.symm inverseMap V K G
  inverseWeight : X × Ω → ℝ
  weight_measurable : Measurable inverseWeight
  weightBound : ℝ
  weight_bounded : ∀ x ∈ K, ∀ ω, inverseWeight (x, ω) ≤ weightBound
  weight_positive : ∀ x ∈ K, ∀ ω, 0 < inverseWeight (x, ω)
  reference : Measure X
  reference_finite : IsFiniteMeasure reference
  reference_support : reference.support = K
  density : X → ℝ
  density_measurable : Measurable density
  density_nonnegative : ∀ x, 0 ≤ density x
  density_continuous : ContinuousOn density K
  density_representation : ν.map Subtype.val = eigenvectorMeasure reference density
  duality : KernelAdjointDensity.IsAdjoint
    (WeightedConditioning.normalizedKernel (RandomMapKernel.killed noise F hF K hK.measurableSet)
      (SubtypeKernel.zeroExtend K w) R (SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hw))
    (WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) reference
  inverse_density_continuous : ContinuousOn
    (fun x => ∫ y, density y ∂(WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) x) K

/-- A full conditional local existence package, including core support. All
process conclusions are derived from analytic separation and the actual
forward/inverse geometry. The density producer supplies only the classical
regularity and change-of-variables inputs for the represented left measure. -/
theorem exists_noise_tolerance_for_full_compared_local_package
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (noise : Measure Ω) [IsProbabilityMeasure noise] [noise.IsOpenPosMeasure]
    (w : K → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ForwardPlaqueInputs T F V K G →
      ∀ (hSF : RestrictedStrongFeller.HasStrongFellerNoise noise F hF),
      let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
      let P := RestrictedStrongFeller.rawTransferOperator noise F hF K hK.measurableSet
        w hw (fun x => (hwpos x).le) R hR hwR hSF
      ∀ s : ComparedRawSpectralInputs (A := A) (W := W) C
        (RestrictedStrongFeller.hasStrongFeller_chain noise F hF K hK.measurableSet
          w hw (fun x => (hwpos x).le) R hR hwR hSF) R,
      (∀ (ν : Measure K) [IsFiniteMeasure ν],
        (∀ f : K →ᵇ ℝ, s.mean f = ∫ y, f y ∂ν) →
        Nonempty (InverseDensityInputs T V K G hK noise F hF w hw.measurable R ν δ)) →
      ∃ ν : Measure K, IsFiniteMeasure ν ∧
        (∀ f : K →ᵇ ℝ, s.mean f = ∫ y, f y ∂ν) ∧
        C.IsQuasiErgodic (eigenvectorMeasure ν s.eigenvector) ∧
        (eigenvectorMeasure ν s.eigenvector).support ⊆ retainedRegion K U ∧
        (∀ x : K, x.val ∈ isolatedCore T K → 0 < s.eigenvector x) ∧
        ({x : K | x.val ∈ isolatedCore T K} ⊆ (eigenvectorMeasure ν s.eigenvector).support) ∧
        (∀ η : Measure K, C.IsQuasiErgodic η →
          {x : K | x.val ∈ isolatedCore T K} ⊆ η.support → η = eigenvectorMeasure ν s.eigenvector) ∧
        (∀ v : K →ᵇ ℝ, P v = s.rate • v → v = s.mean v • s.eigenvector) ∧
        spectralRadius ℝ P = ENNReal.ofReal s.rate := by
  obtain ⟨δf, hδf, hlocal⟩ := LocalQuasiErgodic.exists_noise_tolerance_for_local_package
    T V K G U hV hVK hK hG hU hcoreU hUV hsep hcoreG htrans hcore noise w hw hwpos R hR hwR
  have hcoreV : isolatedCore T K ⊆ V := hcoreU.trans (subset_closure.trans hUV)
  obtain ⟨δi, hδi, hinverse⟩ := exists_noise_tolerance_for_inverse_support_from_actual_data
    (Ω := Ω) T V K G U hV hVK hK hG hcoreV hcoreG htrans hUV
  refine ⟨min δf δi, lt_min hδf hδi, ?_⟩
  intro F hF hclose hp hSF
  dsimp only
  intro s hdensity
  obtain ⟨d, hdr, hdμ, hdg⟩ := s.exists_rawRankOne
  let d' : RankOneSpectralData
      (RestrictedStrongFeller.rawTransferOperator noise F hF K hK.measurableSet
        w hw (fun x => (hwpos x).le) R hR hwR hSF) (1 : K →ᵇ ℝ) := d
  obtain ⟨ν, hν, hm, hq, hloc, hgpos, hunique, hsimp⟩ := hlocal F hF
    (fun x hx ω => (hclose x hx ω).trans_le (min_le_left _ _)) hp hSF d'
  let : IsFiniteMeasure ν := hν
  have hdr' : d'.rate = s.rate := hdr
  have hdμ' : d'.mean = s.mean := hdμ
  have hdg' : d'.eigenvector = s.eigenvector := hdg
  have hmS : ∀ f : K →ᵇ ℝ, s.mean f = ∫ y, f y ∂ν := by simpa only [hdμ'] using hm
  obtain ⟨cert⟩ := hdensity ν hmS
  let : IsFiniteMeasure cert.reference := cert.reference_finite
  let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
  let hSFk := RestrictedStrongFeller.hasStrongFeller_chain noise F hF K hK.measurableSet
    w hw (fun x => (hwpos x).le) R hR hwR hSF
  let dn := d'.ofRawNormalization R hR
    (RestrictedStrongFeller.inv_smul_rawTransferOperator noise F hF K hK.measurableSet
      w hw (fun x => (hwpos x).le) R hR hwR hSF)
  have hdnμ : dn.mean = d'.mean := d'.ofRawNormalization_mean _ _ _
  have hdng : dn.eigenvector = d'.eigenvector := d'.ofRawNormalization_eigenvector _ _ _
  have hsupport := hinverse noise F hF w hw.measurable R hR hwR hSFk dn ν
    (by simpa only [hdnμ] using hm) (by simpa only [hdng] using hloc)
    (by simpa only [hdng] using hgpos) cert.inverseMap cert.inverse_measurable
    (fun x hx ω => (cert.inverse_close x hx ω).trans_le (min_le_right _ _)) cert.inverse_plaques
    cert.inverseWeight cert.weight_measurable cert.weightBound cert.weight_bounded cert.weight_positive
    cert.reference cert.density cert.reference_support cert.density_measurable
    cert.density_nonnegative cert.density_continuous cert.density_representation
    cert.duality cert.inverse_density_continuous
  refine ⟨ν, hν, hmS, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hdg'] using hq
  · simpa only [hdg'] using hloc
  · simpa only [hdg'] using hgpos
  · simpa only [hdng, hdg'] using hsupport
  · simpa only [hdg'] using hunique
  · simpa only [hdr', hdμ', hdg'] using hsimp
  · rw [← hdr']
    exact d'.spectralRadius_eq_rate

end ConditionedStochasticStabilityHyperbolic.ComparedLocalQuasiErgodic
