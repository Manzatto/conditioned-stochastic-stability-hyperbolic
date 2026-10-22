module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalKLPointwise
public import ConditionedStochasticStabilityHyperbolic.Global.UniformNoFullSupportStrongFellerQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.SameCutoffClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.ConstructedInvariantPairing
public import ConditionedStochasticStabilityHyperbolic.Spectral.CutoffHarmonicSupport

/-! Pointwise local QEM and physical pairing from the same two-weight
analytic spectral application. Both physical gaps and both represented
leading measures are constructed; supported common-core source facts then
produce the actual pairing packet used for the weak limit. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLPointwise
open LeanShared Restriction KellerLiverani1999 LocalPositiveCollar
open LeanShared.ControlledPlaqueClosure

variable {H W Z Zret Core X Ω : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

open LocalKLPointwise

set_option maxHeartbeats 800000 in
theorem exists_uniform_pointwise_local_pairing_package
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ η : ℝ, 0 < η ∧ ∀ (noise : Measure Ω) [IsProbabilityMeasure noise] [noise.IsOpenPosMeasure]
      (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < η) →
      ForwardCollarPlaqueInputs T F V K G →
      ∀ (wc : K → ℝ) (hwc : Measurable wc) (hwcR : ∀ x, wc x ≤ R),
      let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
      let D := RestrictedNoise.chain noise F hF K hK.measurableSet wc hwc R hR hwcR
      ∀ (hSF : HasStrongFellerKernel C) (hSD : HasStrongFellerKernel D),
      ∀ {P : ℝ≥0 → H →L[ℂ] H} {weak : H →L[ℂ] W}
        {det : DeterministicLeading (P 0)} {q δ : ℝ}
        (o : ProjectorOutputs P weak det q δ),
      δ < q - det.subordinate → δ < det.rate - q → 0 < q →
      ∀ ε : ℝ≥0,
      SameCutoffClassicalSources (Z := Z) (Zret := Zret) o ε D C hSD hSF R →
      NoFullSupportCollarDensityCertificate.Inputs T V K G hK noise F hF w hw.measurable R η →
      ∀ (γ : H) (ma : H →L[ℂ] ℂ), o.projection ε = ma.smulRight γ →
      ∀ (A : Set (K →ᵇ ℝ)) (M : A → H →L[ℂ] H),
      (∀ (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hSD)
          (1 : K →ᵇ ℝ)) (μcut : Measure K) [IsFiniteMeasure μcut],
        (∀ f : K →ᵇ ℝ, dc.mean f = ∫ x, f x ∂μcut) →
        Nonempty (SupportedCoreSources (Z := Z) (Core := Core)
          (o.projection ε) (((o.eigenvalue ε).re : ℂ)⁻¹ • P ε) D hSD dc μcut wc A M)) →
      ∃ ν : ProbabilityMeasure K,
        C.IsQuasiErgodic (ν : Measure K) ∧
        (ν : Measure K).support ⊆ retainedRegion K U ∧
        {x : K | x.val ∈ isolatedCore T K} ⊆ (ν : Measure K).support ∧
        (∀ ζ : Measure K, C.IsQuasiErgodic ζ →
          {x : K | x.val ∈ isolatedCore T K} ⊆ ζ.support → ζ = (ν : Measure K)) ∧
        Nonempty (InvariantPhysicalPairing.Inputs (Z := Z) (Core := Core)
          (o.projection ε) (((o.eigenvalue ε).re : ℂ)⁻¹ • P ε) γ ν A M) := by
  obtain ⟨η, hη, hlocal⟩ := UniformNoFullSupportCollarQuasiErgodic.exists_uniform_noise_tolerance_for_full_collar_chain_package
    (Ω := Ω) T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore w hw hwG R hR hwR
  refine ⟨η, hη, ?_⟩
  intro noise _ _ F hF hclose hp wc hwc hwcR
  dsimp only
  intro hSF hSD P weak det q δ o hδsub hδlead hq ε s c γ ma hPa A M hcores
  let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
  let D := RestrictedNoise.chain noise F hF K hK.measurableSet wc hwc R hR hwcR
  let so := s.originalInputs o hδsub hδlead hq ε D C hSD hSF R hR
  let sc := s.cutoffInputs o hδsub hδlead hq ε D C hSD hSF R hR
  obtain ⟨dor, hrateo, _honeo⟩ := so.exists_gap
  obtain ⟨dcraw, hratec, _honec⟩ := sc.exists_gap
  obtain ⟨μoriginal, hμoriginal, hmoriginal, hqem, hlocalo, _hpositive, hsupp, hunique, _hsimp, _hradius⟩ :=
    hlocal noise F hF hclose hp hSF dor c
  let : IsFiniteMeasure μoriginal := hμoriginal
  let dn := CanonicalChainGap.normalized C hSF R hR dor
  let dc := CanonicalChainGap.normalized D hSD R hR dcraw
  have hmoriginal' : ∀ f : K →ᵇ ℝ, dn.mean f = ∫ x, f x ∂μoriginal := by
    simpa only [dn, CanonicalChainGap.normalized_mean] using hmoriginal
  let : IsFiniteKernel D.killedTransition := by
    change IsFiniteKernel D.toKilledKernel.kernel
    infer_instance
  let dr := dcraw.ofRawNormalization R hR (by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hR), one_smul])
  let μcut := rankOneKernelMeasure D.killedTransition (strongFellerTransferOperator D hSD)
    (strongFellerTransferOperator_represents D hSD) dr
  have hmcut : ∀ f : K →ᵇ ℝ, dc.mean f = ∫ x, f x ∂μcut := by
    intro f
    rw [show dc.mean = dcraw.mean from CanonicalChainGap.normalized_mean D hSD R hR dcraw]
    have hh := dr.eigenmeasure_represents
      (representedTransfer_positive D.killedTransition (strongFellerTransferOperator D hSD)
        (strongFellerTransferOperator_represents D hSD)) f
    simpa only [μcut, rankOneKernelMeasure, dr, RankOneSpectralData.ofRawNormalization_mean] using hh
  let : IsProbabilityMeasure (eigenvectorMeasure μoriginal dn.eigenvector) := by
    rw [CanonicalChainGap.normalized_eigenvector]
    exact hqem.1
  let ν : ProbabilityMeasure K := ⟨eigenvectorMeasure μoriginal dn.eigenvector, inferInstance⟩
  have hrate : dn.rate = dc.rate := by
    simp only [dn, dc, CanonicalChainGap.normalized_rate]
    rw [hrateo, hratec]
    rfl
  obtain ⟨cs⟩ := hcores dc μcut hmcut
  have hcutSupport : tsupport (AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector) ⊆
      cs.core.supportedRegion := by
    have hh := CutoffHarmonicSupport.tsupport_eigenvector_subset_weight
      noise F hF K hK.measurableSet wc hwc R hR hwcR hSD dr
    simpa only [dc, dr, CanonicalChainGap.normalized_eigenvector,
      RankOneSpectralData.ofRawNormalization_eigenvector] using hh.trans cs.weightSupport
  have hI := ConstructedInvariantPairing.exists_inputs_of_actual_gaps_and_core
    C D hSF hSD s.V s.BD s.BC s.hV s.heq.symm
    s.hreturnD s.hextD s.hreturnC s.hextC s.ND s.NC s.hcompD s.hcompC
    dn dc hrate μoriginal μcut hmoriginal' hmcut ν rfl
    (o.projection ε) (((o.eigenvalue ε).re : ℂ)⁻¹ • P ε) γ ma hPa A M cs.core hcutSupport
  refine ⟨ν, ?_, ?_, ?_, ?_, hI⟩
  · simpa only [ν, ProbabilityMeasure.coe_mk, dn, CanonicalChainGap.normalized_eigenvector] using hqem
  · simpa only [ν, ProbabilityMeasure.coe_mk, dn, CanonicalChainGap.normalized_eigenvector] using hlocalo
  · simpa only [ν, ProbabilityMeasure.coe_mk, dn, CanonicalChainGap.normalized_eigenvector] using hsupp
  · simpa only [ν, ProbabilityMeasure.coe_mk, dn, CanonicalChainGap.normalized_eigenvector] using hunique

end ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLPointwise
