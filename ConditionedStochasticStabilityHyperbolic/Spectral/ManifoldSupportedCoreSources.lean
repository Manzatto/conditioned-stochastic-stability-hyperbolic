module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ManifoldRegularCoreRealization
public import ConditionedStochasticStabilityHyperbolic.Spectral.ConstructedSupportedCoreSources
public import LeanShared.Geometry.SupportedCoreMultipliers
public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonRegularProjectors

/-! Concrete supported-core source construction for the manifold front end.
The common regular realization and literal smooth multiplication are built,
not requested as fields of a model-specific factory. Remaining classical
facts are explicit smooth-core bounds, supported approximation, faithful
function/distribution embedding, and SAME-cutoff Riesz comparison. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.ManifoldSupportedCoreSources
open LeanShared.SmoothSupportedManifoldCore RegularCoreApproximation

variable {E M Reg H Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  (V K : Set M) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
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

/-- Literal restricted smooth functions, retaining their actual values. -/
def liveFunctions : core (E := E) V →ₗ[ℂ] (K → ℂ) where
  toFun c x := functions V c x.val
  map_add' _c _d := rfl
  map_smul' _a _c := rfl

/-- Build the full invariant-core packet from the constructed regular
realization. Action laws need only be checked on actual supported smooth
functions (and are produced by `ActualInvariantCoreAverage`). -/
def coreSources
    (C : AbsorbingMarkovChains.CanonicalChain K) (hSF : HasStrongFellerKernel C)
    (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF)
      (1 : K →ᵇ ℝ)) (μ : Measure K) [IsFiniteMeasure μ]
    (Pa Pm : H →L[ℂ] H) (leadingRate : ℝ) (hrate : dc.rate = leadingRate)
    (T : Reg →L[ℂ] Reg)
    (hactionA : ∀ c, realize (T (q c)) = Pm (realize (q c)))
    (hactionP : ∀ c, physicalRealization V K q (T (q c)) =
      ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF (physicalRealization V K q (q c)))
    (a : H →L[ℂ] Z) (b : (K →ᵇ ℂ) →L[ℂ] Z) (O : Set K)
    (hsupportedDense : ∀ f : K →ᵇ ℂ, tsupport f ⊆ O →
      f ∈ closure (range (physicalCore (E := E) V K)))
    (hfaithful : ∀ f : K →ᵇ ℂ, tsupport f ⊆ O → b f = 0 → f = 0)
    (hprojector : ∀ c, b ((ComplexLeadingMeasure.integralFunctional μ).smulRight
      (AbsorbingMarkovChains.ComplexKernel.ofReal dc.eigenvector) (physicalCore V K c)) =
      a (Pa (qa c)))
    (r t s u : ℝ) (hmargins : RegularityMargins r t s u) :
    ConstructedInvariantPairing.CoreSources (Z := Z) (Core := Reg)
      Pa ((leadingRate : ℂ)⁻¹ • Pm) C hSF dc μ A
      (fun h => ConstructedRegularMultipliers.analyticMultiplier qa (multiplier V (test h) (htest h))) := by
  let D := ManifoldRegularCoreRealization.realization V K q dense realize
  have hp : ∀ c, D.physical (D.smooth c) = physicalCore V K c :=
    physicalRealization_core V K q dense C0 hC0
  apply ConstructedSupportedCoreSources.coreSourcesOfSmoothFacts D q (fun _ => rfl)
    qa hqa hrealize A (fun h => multiplier V (test h) (htest h))
    (liveFunctions V K)
    (fun c x => congrArg (fun f : K →ᵇ ℂ => f x) (hp c))
    (fun h c x => by change functions V c x.val * test h x.val = _; rw [htestLive]; rfl)
    CR CA hregular hanalytic C hSF dc μ Pa Pm leadingRate hrate T
    hactionA hactionP a b O ?_ hfaithful ?_ r t s u hmargins
  · intro f hf
    convert hsupportedDense f hf using 1
    congr 2
    funext c
    exact hp c
  · intro c
    rw [hp]
    change _ = a (Pa (realize (q c)))
    rw [hrealize]
    exact hprojector c

/-- The classical projector-comparison premise is eliminated by actual common
regular powers and both produced gaps. Only literal common-function embedding
compatibility remains. -/
def coreSourcesFromCommonFunctionsAndPowers
    (C : AbsorbingMarkovChains.CanonicalChain K) (hSF : HasStrongFellerKernel C)
    (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF)
      (1 : K →ᵇ ℝ)) (μ : Measure K) [IsFiniteMeasure μ]
    (Pa Pm : H →L[ℂ] H) (leadingRate : ℝ) (hrate : dc.rate = leadingRate)
    (T : Reg →L[ℂ] Reg)
    (hactionA : ∀ c, realize (T (q c)) = Pm (realize (q c)))
    (hactionP : ∀ c, physicalRealization V K q (T (q c)) =
      ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF (physicalRealization V K q (q c)))
    (a : H →L[ℂ] Z) (b : (K →ᵇ ℂ) →L[ℂ] Z) (O : Set K)
    (hsupportedDense : ∀ f : K →ᵇ ℂ, tsupport f ⊆ O →
      f ∈ closure (range (physicalCore (E := E) V K)))
    (hfaithful : ∀ f : K →ᵇ ℂ, tsupport f ⊆ O → b f = 0 → f = 0)
    (hμ : ∀ f : K →ᵇ ℝ, dc.mean f = ∫ x, f x ∂μ)
    (hcommon : ∀ c, b (physicalCore V K c) = a (qa c))
    (hpower : Filter.Tendsto (fun n : ℕ => ((dc.rate : ℂ)⁻¹ • Pm)^n)
      Filter.atTop (𝓝 Pa))
    (r t s u : ℝ) (hmargins : RegularityMargins r t s u) :
    ConstructedInvariantPairing.CoreSources (Z := Z) (Core := Reg)
      Pa ((leadingRate : ℂ)⁻¹ • Pm) C hSF dc μ A
      (fun h => ConstructedRegularMultipliers.analyticMultiplier qa (multiplier V (test h) (htest h))) := by
  have hA : realize.comp T = Pm.comp realize := by
    apply ContinuousLinearMap.ext
    intro v
    exact dense.induction_on (p := fun v => realize (T v) = Pm (realize v)) v
      (isClosed_eq (realize.continuous.comp T.continuous)
        (Pm.continuous.comp realize.continuous)) hactionA
  have hP : (physicalRealization V K q).comp T =
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF).comp (physicalRealization V K q) := by
    apply ContinuousLinearMap.ext
    intro v
    exact dense.induction_on
      (p := fun v => physicalRealization V K q (T v) =
        ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF (physicalRealization V K q v)) v
      (isClosed_eq ((physicalRealization V K q).continuous.comp T.continuous)
        ((ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF).continuous.comp
          (physicalRealization V K q).continuous)) hactionP
  apply coreSources V K q dense C0 hC0 realize qa hqa hrealize A test htest htestLive
    CR CA hregular hanalytic C hSF dc μ Pa Pm leadingRate hrate T hactionA hactionP
    a b O hsupportedDense hfaithful ?_ r t s u hmargins
  intro c
  have hp := CommonRegularProjectors.comparison_of_actual_gap q dense realize
    (physicalRealization V K q) a b T Pm C hSF dc μ hμ hA hP
    (fun c => by rw [physicalRealization_core V K q dense C0 hC0, hrealize]; exact hcommon c)
    Pa hpower (q c)
  rw [physicalRealization_core V K q dense C0 hC0, hrealize] at hp
  exact hp

end ConditionedStochasticStabilityHyperbolic.ManifoldSupportedCoreSources
