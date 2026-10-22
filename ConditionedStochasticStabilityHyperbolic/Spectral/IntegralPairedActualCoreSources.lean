module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualManifoldKLCoreSources
public import LeanShared.Geometry.SmoothDistributionPairing

/-! Final supported-core source from literal actual regular/analytic averages.
Neither completed physical intertwining, common-core invariance nor Riesz
projector comparison is assumed. All are derived from smooth core realization
and ordinary little-Hölder weighted composition. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.IntegralPairedActualCoreSources
open LeanShared.SmoothSupportedManifoldCore RegularCoreApproximation KellerLiverani1999

variable {E M Reg H Zret W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  (V K : Set M) [CompactSpace K]
  (q : core (E := E) V →ₗ[ℂ] Reg) (dense : DenseRange q)
  (C0 : ℝ) (hC0 : ∀ c, ‖physicalCore V K c‖ ≤ C0 * ‖q c‖)
  (realize : Reg →L[ℂ] H)
  (qa : core (E := E) V →ₗ[ℂ] H) (hqa : DenseRange qa)
  (hrealize : ∀ c, realize (q c) = qa c)
  (A : Set (K →ᵇ ℝ))
  (test : A → M → ℂ)
  (htest : ∀ h, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (test h))
  (htestLive : ∀ h (x : K), test h x.val = (h.val x : ℂ))
  (CR CA : A → ℝ) (hCR : ∀ h, 0 ≤ CR h) (hCA : ∀ h, 0 ≤ CA h)
  (hregular : ∀ h c, ‖q (multiplier V (test h) (htest h) c)‖ ≤ CR h * ‖q c‖)
  (hanalytic : ∀ h c, ‖qa (multiplier V (test h) (htest h) c)‖ ≤ CA h * ‖qa c‖)



def sourceOfActualAverages
    {P : ℝ≥0 → H →L[ℂ] H} {weak : H →L[ℂ] W}
    {det : DeterministicLeading (P 0)} {qcut δ : ℝ}
    (o : ProjectorOutputs P weak det qcut δ)
    (hδsub : δ < qcut - det.subordinate) (hδlead : δ < det.rate - qcut) (hq : 0 < qcut)
    (ε : ℝ≥0)
    (C D : AbsorbingMarkovChains.CanonicalChain K)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
    (R : ℝ) (hR : 0 < R)
    (s : SameCutoffClassicalSources (Z := (Reg →L[ℂ] ℂ)) (Zret := Zret) o ε D C hD hC R)
    (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD)
      (1 : K →ᵇ ℝ)) (μ : Measure K) [IsFiniteMeasure μ]
    (hμ : ∀ f : K →ᵇ ℝ, dc.mean f = ∫ x, f x ∂μ)
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (view : Reg →ₗ[ℂ] (M → ℂ)) (hview : Function.Injective view)
    (evaluate : M → Reg →L[ℂ] ℂ) (hevaluate : ∀ x v, evaluate x v = view v x)
    (hviewCore : ∀ c, view (q c) = functions V c) (hVK : V ⊆ K)
    (F : Ω → M → M) (g : M → ℝ)
    (hInvariant : ∀ aNoise f, LeanShared.FiniteRegularTransferRealization.weightedComposition
      (F aNoise) g (view f) ∈ view.range)
    (Creg : ℝ) (hCreg : 0 ≤ Creg)
    (hregBound : ∀ aNoise f,
      ‖LeanShared.InvariantFiniteRegularTransfer.action view hview F g hInvariant aNoise f‖ ≤ Creg * ‖f‖)
    (hregMeas : ∀ f, AEStronglyMeasurable (fun aNoise =>
      LeanShared.InvariantFiniteRegularTransfer.operator view hview F g hInvariant Creg hregBound aNoise f) ρ)
    (An : Ω → H →L[ℂ] H)
    (hAnMeas : ∀ f, AEStronglyMeasurable (fun aNoise => An aNoise f) ρ)
    (Can : ℝ) (hAnBound : ∀ aNoise, ‖An aNoise‖ ≤ Can)
    (hanalyticCore : ∀ aNoise c, realize
      (LeanShared.InvariantFiniteRegularTransfer.action view hview F g hInvariant aNoise (q c)) =
      An aNoise (realize (q c)))
    (hF : Measurable (fun z : M × Ω => F z.2 z.1))
    (hK : MeasurableSet K) (wcLive : K → ℝ) (hwcLive : Measurable wcLive)
    (hwc0 : ∀ x, 0 ≤ wcLive x) (hwcR : ∀ x, wcLive x ≤ R)
    (hweight : ∀ x : K, g x.val = wcLive x)
    (hDactual : D = RestrictedNoise.chain ρ (fun z => F z.2 z.1) hF K hK wcLive hwcLive R hR hwcR)
    (hPactual : P ε = (((R⁻¹ : ℝ) : ℂ) •
      LeanShared.AnnealedOperatorBounds.pointwiseAnnealed ρ An hAnMeas Can hAnBound))
    (hKclosed : IsClosed K) (hVopen : IsOpen V)
    (σ : Measure K) [IsFiniteMeasure σ]
    (hpositive : {x : K | x.val ∈ V} ⊆ σ.support)
    (a : H →L[ℂ] (Reg →L[ℂ] ℂ))
    (hsmoothPairing : ∀ c d, a (qa c) (q d) =
      ∫ x : K, functions V c x.val * functions V d x.val ∂σ)
    (hsupport : tsupport wcLive ⊆ {x : K | x.val ∈ V})
    (r t sn u : ℝ) (hmargins : RegularityMargins r t sn u) :
    LocalKLPointwise.SupportedCoreSources (Z := (Reg →L[ℂ] ℂ)) (Core := Reg)
      (o.projection ε) (((o.eigenvalue ε).re : ℂ)⁻¹ • P ε) D hD dc μ wcLive A
      (fun h => ConstructedRegularMultipliers.analyticMultiplier qa (multiplier V (test h) (htest h))) := by
  let physical := physicalRealization V K q
  have hphysical : ∀ c, physical (q c) = physicalCore V K c :=
    physicalRealization_core V K q dense C0 hC0
  let b := LeanShared.SupportedRegularPairing.embedding σ physical
  have hcommon : ∀ c, b (physicalCore V K c) = a (qa c) := fun c =>
    (common_identity_of_smooth_tests σ q dense physical hphysical qa a hsmoothPairing c).symm
  exact ActualManifoldKLCoreSources.sourceOfActualAverages V K q dense C0 hC0
    realize qa hqa hrealize A test htest htestLive CR CA hregular hanalytic
    o hδsub hδlead hq ε C D hC hD R hR s dc μ hμ ρ
    view hview evaluate hevaluate hviewCore hVK F g hInvariant Creg hCreg hregBound hregMeas
    An hAnMeas Can hAnBound hanalyticCore hF hK wcLive hwcLive hwc0 hwcR hweight hDactual hPactual
    a b {x : K | x.val ∈ V}
    (fun f hf => physicalCore_supported_dense hKclosed hVopen f hf)
    (physical_pairing_faithful hKclosed hVopen σ q physical hphysical hpositive)
    hcommon hsupport r t sn u hmargins

end ConditionedStochasticStabilityHyperbolic.IntegralPairedActualCoreSources
