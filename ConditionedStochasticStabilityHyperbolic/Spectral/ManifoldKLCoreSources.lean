module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ManifoldSupportedCoreSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.SameCutoffRate
public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalKLPointwise
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniRieszGap

/-! The universal supported-core source in the local KL consumer is a constructed manifold model.
Arbitrary physical pair choices receive their rate from the actual same-cutoff spectral
correspondence. Invariance and common powers derive the projector law; no source factory is
assumed. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.ManifoldKLCoreSources
open LeanShared.SmoothSupportedManifoldCore RegularCoreApproximation KellerLiverani1999

variable {E M Reg H Z Zret W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
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

/-- Construct the exact pointwise source consumed by the family theorem. The
smooth action hypotheses come from the literal constructed regular average;
all whole-regular-space identities and Riesz projector compatibility are derived. -/
def sourceOfActualModel
    {P : ℝ≥0 → H →L[ℂ] H} {weak : H →L[ℂ] W}
    {det : DeterministicLeading (P 0)} {qcut δ : ℝ}
    (o : ProjectorOutputs P weak det qcut δ)
    (hδsub : δ < qcut - det.subordinate) (hδlead : δ < det.rate - qcut) (hq : 0 < qcut)
    (ε : ℝ≥0)
    (C D : AbsorbingMarkovChains.CanonicalChain K)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
    (R : ℝ) (hR : 0 < R)
    (s : SameCutoffClassicalSources (Z := Z) (Zret := Zret) o ε D C hD hC R)
    (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD)
      (1 : K →ᵇ ℝ)) (μ : Measure K) [IsFiniteMeasure μ]
    (hμ : ∀ f : K →ᵇ ℝ, dc.mean f = ∫ x, f x ∂μ)
    (Treg : Reg →L[ℂ] Reg)
    (hactionA : ∀ c, realize (Treg (q c)) = P ε (realize (q c)))
    (hactionP : ∀ c, physicalRealization V K q (Treg (q c)) =
      ComplexStrongFeller.transferOperator (𝕜 := ℂ) D hD (physicalRealization V K q (q c)))
    (a : H →L[ℂ] Z) (b : (K →ᵇ ℂ) →L[ℂ] Z) (O : Set K)
    (hsupportedDense : ∀ f : K →ᵇ ℂ, tsupport f ⊆ O →
      f ∈ closure (range (physicalCore (E := E) V K)))
    (hfaithful : ∀ f : K →ᵇ ℂ, tsupport f ⊆ O → b f = 0 → f = 0)
    (hcommon : ∀ c, b (physicalCore V K c) = a (qa c))
    (wc : K → ℝ) (hsupport : tsupport wc ⊆ O)
    (r t sn u : ℝ) (hmargins : RegularityMargins r t sn u) :
    LocalKLPointwise.SupportedCoreSources (Z := Z) (Core := Reg)
      (o.projection ε) (((o.eigenvalue ε).re : ℂ)⁻¹ • P ε) D hD dc μ wc A
      (fun h => ConstructedRegularMultipliers.analyticMultiplier qa (multiplier V (test h) (htest h))) := by
  have hr := s.normalized_cutoff_rate o hδsub hδlead hq ε D C hD hC R hR dc
  have hpower : Tendsto (fun n : ℕ => ((dc.rate : ℂ)⁻¹ • P ε)^n) atTop (𝓝 (o.projection ε)) := by
    rw [hr]
    exact o.tendsto_normalized_powers hδsub hδlead hq ε s.parameterSmall s.conjugation
  exact ⟨ManifoldSupportedCoreSources.coreSourcesFromCommonFunctionsAndPowers
    V K q dense C0 hC0 realize qa hqa hrealize A test htest htestLive CR CA hregular hanalytic
    D hD dc μ (o.projection ε) (P ε) (o.eigenvalue ε).re hr Treg hactionA hactionP
    a b O hsupportedDense hfaithful hμ hcommon hpower r t sn u hmargins, hsupport⟩

end ConditionedStochasticStabilityHyperbolic.ManifoldKLCoreSources
