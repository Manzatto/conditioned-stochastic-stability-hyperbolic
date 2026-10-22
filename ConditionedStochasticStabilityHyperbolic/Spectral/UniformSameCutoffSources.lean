module

public import ConditionedStochasticStabilityHyperbolic.Spectral.SameCutoffClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Restriction.UniformNoiseLocalization
public import ConditionedStochasticStabilityHyperbolic.Restriction.WeightAgreement

/-! The actual local geometry constructs the retained-region spectral source
uniformly before the driving law. Only the cited same-cutoff comparison and
standard compact spectral theorems remain source inputs. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open LeanShared Restriction

variable {E W Z Zret X Ω : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MeasurableSpace Ω]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

/-- Exact cited Appendix-A same-operator comparisons, and the classical
power-compact spectral sources. Geometric extinction is deliberately absent. -/
structure ClassicalSameCutoffComparisons
    (o : ProjectorOutputs P i d q δ) (ε : ℝ≥0)
    {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (C : AbsorbingMarkovChains.CanonicalChain Y) (hC : HasStrongFellerKernel C)
    (R : ℝ) (V : Set Y) where
  parameterSmall : ε ≤ o.window
  conjugation : RealOperatorConjugation (P ε)
  analyticAmbient : E →L[ℂ] Z
  physicalAmbient : (Y →ᵇ ℂ) →L[ℂ] Z
  restriction : Z →L[ℂ] Zret
  retainedAmbient : (V →ᵇ ℂ) →L[ℂ] Zret
  retained_injective : Function.Injective retainedAmbient
  restriction_identity : restriction.comp physicalAmbient = retainedAmbient.comp (restrictObservable V)
  ordinary : ComparedSpectralGap.EigenvectorComparison ((R : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      analyticAmbient physicalAmbient (R * q)
  generalized : GeneralizedSpectralComparison.Comparison ((R : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      analyticAmbient physicalAmbient ((R * (o.eigenvalue ε).re : ℝ) : ℂ)
  reverse : CutoffEigenvectorLifting.ClassicalRealization ((R : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      analyticAmbient physicalAmbient (R * q)
  ultraFeller : StrongFellerSquareCompact.UltraFellerContract (X := Y)
  fredholm : PowerCompactGap.SquareCompactFredholm (F := Y →ᵇ ℂ)
  riesz : PowerCompactRealLeadingPair.ClassicalContract (X := Y)

omit [CompleteSpace E] in
/-- One geometric tolerance works for every law, both actual weights and all
classical comparison outputs. Neither spectral simplicity nor a gap is supplied. -/
theorem exists_uniform_same_cutoff_sources
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) [CompactSpace K] (hU : IsOpen U)
    (hcore : isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U) :
    ∃ η : ℝ, 0 < η ∧ ∀ (ρ : Measure Ω) [IsProbabilityMeasure ρ]
      (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ z, dist (F (x, z)) (T x) < η) →
      ∀ (w wc : K → ℝ) (hw : Measurable w) (hwc : Measurable wc)
      (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R),
      (∀ x : K, x.val ∈ closure U → wc x = w x) →
      let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw R hR hwR
      let D := RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc R hR hwcR
      ∀ (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
      (o : ProjectorOutputs P i d q δ) (ε : ℝ≥0),
      ClassicalSameCutoffComparisons (Z := Z) (Zret := Zret)
        o ε D hD R (retainedRegion K U) →
      Nonempty (SameCutoffClassicalSources (Z := Z) (Zret := Zret) o ε D C hD hC R) := by
  obtain ⟨r₀, hr₀, hnonreturn⟩ := exists_uniform_nonreturn T.continuous
    isClosed_closure.isCompact (isClosed_forwardTrapped T.continuous hK.isClosed) hU hsep
  let S := Metric.thickening r₀ (forwardTrapped T K)
  obtain ⟨N, _hN, η, hη, hcert⟩ := UniformNoiseLocalization.exists_uniform_geometric_lifting_certificates
    (Ω := Ω) T K U S hK hU Metric.isOpen_thickening hcore
      (Metric.self_subset_thickening hr₀ _)
  refine ⟨min η r₀, lt_min hη hr₀, ?_⟩
  intro ρ _ F hF hclose w wc hw hwc R hR hwR hwcR heq
  dsimp only
  intro hC hD o ε s
  have hnear : ∀ x ∈ K, ∀ z, dist (F (x, z)) (T x) < η :=
    fun x hx z => (hclose x hx z).trans_le (min_le_left _ _)
  have hno : ∀ x ∈ K, x ∈ closure U → ∀ z, F (x, z) ∉ S \ U := by
    intro x _hx hx z
    exact hnonreturn (fun y => F (y, z))
      (fun y hy => (hclose y (hUK hy) z).trans_le (min_le_right _ _)) x hx
  obtain ⟨hreturnC, hextC, hcompC⟩ := hcert ρ w hw R hR hwR F hF hnear hno
  obtain ⟨hreturnD, hextD, hcompD⟩ := hcert ρ wc hwc R hR hwcR F hF hnear hno
  let V := retainedRegion K U
  have hV : MeasurableSet V := isClosed_closure.measurableSet.preimage measurable_subtype_coe
  refine ⟨{
    parameterSmall := s.parameterSmall
    conjugation := s.conjugation
    V := V
    BC := badRegion K S
    BD := badRegion K S
    hV := hV
    heq := restricted_weighted_kernel_eq ρ F hF K hK.measurableSet V hV wc w hwc hw R hR hwcR hwR heq
    hreturnC := hreturnD
    hextC := hextD
    hreturnD := hreturnC
    hextD := hextC
    NC := N
    ND := N
    hcompC := hcompD
    hcompD := hcompC
    aSource := s.analyticAmbient
    bSource := s.physicalAmbient
    restrictSource := s.restriction
    ambientRetained := s.retainedAmbient
    hRet := s.retained_injective
    hcompat := s.restriction_identity
    hordinary := s.ordinary
    hgeneral := s.generalized
    hreverse := s.reverse
    hUltra := s.ultraFeller
    hFredholm := s.fredholm
    hRiesz := s.riesz }⟩

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
