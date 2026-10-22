module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldSupportedCore
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldNoiseSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.IntegralPairedActualCoreSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedOperatorIdentity
public import LeanShared.Analysis.InvariantFiniteRegularCompatibility
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalytic
meta import Lean.LibrarySuggestions.Basic

/-! Native companion (one-step core bound instead of row sources): the actual
manifold model supplies the full supported-core source used
by local weak stability. Ordinary smooth multiplication bounds, fractional
distribution embedding and the literal integral identity are the only source
facts; completed core realizations and averaged operators are constructed. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalManifoldSupportedCoreNative"

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSupportedCoreNative
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open SmoothSupportedManifoldCore KellerLiverani1999 RegularCoreApproximation

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

variable (K : Set M) [CompactSpace K] (Tests : Set (K →ᵇ ℝ)) (σ : Measure K) [IsFiniteMeasure σ]

namespace Data
variable (p : PhysicalManifoldSupportedCore.CoreData (K := K) (Tests := Tests) (σ := σ) m.regularCore (coreLift m.qa))

variable [MetricSpace Ω]

def source
    {Lrows : ℝ} (analytic : PhysicalModelAnalytic.AnalyticBound m Lrows) (n : PhysicalManifoldNoiseSources.Data m)
    {Noise W Zret : Type*} [TopologicalSpace Noise] [MeasurableSpace Noise]
    [OpensMeasurableSpace Noise] [SecondCountableTopology Noise]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
    (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
    (noise : ℝ≥0 → Noise → Ω) (hnoise : ∀ ε, Continuous (noise ε))
    (j : m.StrongSpace →L[ℂ] W) (R : ℝ)
    (inputs : ActualAnnealedInputs law (fun _ => inferInstance) j R)
    (hgenerator : ∀ ε z, inputs.generator ε z = m.generator (noise ε z))
    {det : DeterministicLeading (inputs.operator 0)} {qcut δ : ℝ}
    (o : ProjectorOutputs inputs.operator (LeanShared.TwoNormNormalization.weakEmbedding j) det qcut δ)
    (hδsub : δ < qcut - det.subordinate) (hδlead : δ < det.rate - qcut) (hq : 0 < qcut)
    (ε : ℝ≥0) (C D : AbsorbingMarkovChains.CanonicalChain K)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D) (hR : 0 < R)
    (s : SameCutoffClassicalSources (Z := (Reg →L[ℂ] ℂ)) (Zret := Zret) o ε D C hD hC R)
    (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD) (1 : K →ᵇ ℝ))
    (μcut : Measure K) [IsFiniteMeasure μcut]
    (hμ : ∀ f : K →ᵇ ℝ, dc.mean f = ∫ x, f x ∂μcut)
    (hVK : V ⊆ K) (hK : IsClosed K) (hV : IsOpen V)
    (hpositive : {x : K | x.val ∈ V} ⊆ σ.support)
    (hF : Measurable (fun z : M × Noise => m.maps (noise ε z.2) z.1))
    (wc : K → ℝ) (hwc : Measurable wc) (hwc0 : ∀ x, 0 ≤ wc x) (hwcR : ∀ x, wc x ≤ R)
    (hweight : ∀ x : K, m.weight x.val = wc x)
    (hDactual : D = RestrictedNoise.chain (law ε)
      (fun z : M × Noise => m.maps (noise ε z.2) z.1) hF K hK.measurableSet wc hwc R hR hwcR)
    (hsupport : tsupport wc ⊆ {x : K | x.val ∈ V})
    (r t sn u : ℝ) (margins : RegularityMargins r t sn u) :
    LocalKLPointwise.SupportedCoreSources (Z := (Reg →L[ℂ] ℂ)) (Core := Reg)
      (o.projection ε) (((o.eigenvalue ε).re : ℂ)⁻¹ • inputs.operator ε)
      D hD dc μcut wc Tests
      (fun h => ConstructedRegularMultipliers.analyticMultiplier (coreLift m.qa)
        (SmoothSupportedManifoldCore.multiplier V (p.test h) (p.test_smooth h))) := by
  let maps := fun z : Noise => m.maps (noise ε z)
  let invariant := fun z v => m.invariant (noise ε z) v
  let regular := fun z c => m.coreRegular (noise ε z) c
  let bound := max 0 m.regularConstant
  have hbound : ∀ z f, ‖InvariantFiniteRegularTransfer.action m.view m.view_injective
      maps m.weight invariant z f‖ ≤ bound * ‖f‖ := fun z f =>
    (m.regularBound (noise ε z) f).trans
      (mul_le_mul_of_nonneg_right (le_max_right 0 _) (norm_nonneg f))
  have haction (z : Noise) (c : PhysicalManifoldModel.Core (E := E) V) :
      InvariantFiniteRegularTransfer.action m.view m.view_injective maps m.weight invariant z
        (m.regularCore c) = regularAction (functions V) Reg m.view m.view_injective
          maps m.weight regular z c :=
    InvariantFiniteRegularCompatibility.core_action_eq (functions V) m.regularCore m.view
      m.view_injective m.view_core maps m.weight invariant regular z c
  have hcont : ∀ c, Continuous (fun z => InvariantFiniteRegularTransfer.action
      m.view m.view_injective maps m.weight invariant z (m.regularCore c)) := by
    intro c
    exact (n.noise_core_continuous m noise hnoise ε c).congr (fun z => (haction z c).symm)
  have hmeas : ∀ f, AEStronglyMeasurable (fun z =>
      InvariantFiniteRegularTransfer.operator m.view m.view_injective maps m.weight invariant
        bound hbound z f) (law ε) := fun f =>
    (InvariantFiniteRegularTransfer.measurable_orbit m.view m.view_injective maps m.weight
      invariant bound hbound m.regularCore m.regularCore_dense hcont f).aestronglyMeasurable
  have hcore : ∀ z c, m.realize
      (InvariantFiniteRegularTransfer.action m.view m.view_injective maps m.weight invariant z (m.regularCore c)) =
        inputs.generator ε z (m.realize (m.regularCore c)) := by
    intro z c
    have h₁ := congrArg m.realize (haction z c)
    have h₂ := operator_core m.qa (functions V) Reg m.view m.view_injective m.realize
      m.maps m.weight m.coreRegular Lrows analytic (noise ε z) c
    have h₃ := congrArg (fun L : m.StrongSpace →L[ℂ] m.StrongSpace => L (coreLift m.qa c))
      (hgenerator ε z)
    have h₄ := congrArg (inputs.generator ε z) (m.realize_core c)
    exact h₁.trans (h₂.symm.trans (h₃.symm.trans h₄.symm))
  let result := IntegralPairedActualCoreSources.sourceOfActualAverages V K m.regularCore m.regularCore_dense
    p.uniformConstant p.uniformBound m.realize (coreLift m.qa) (coreLift_dense m.qa) m.realize_core
    Tests p.test p.test_smooth p.test_live p.regularConstant p.analyticConstant
    p.regularMultiplierBound p.analyticMultiplierBound o hδsub hδlead hq ε C D hC hD R hR s dc μcut hμ
    (law ε) m.view m.view_injective m.evaluate m.evaluation m.view_core hVK maps m.weight invariant
    bound (le_max_left 0 _) hbound hmeas (inputs.generator ε) (inputs.measurable ε)
    inputs.operatorBound (inputs.generator_bound ε) hcore hF hK.measurableSet wc hwc hwc0 hwcR hweight
    hDactual rfl hK hV σ hpositive p.embedding p.smoothPairing hsupport r t sn u margins
  exact result

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSupportedCoreNative
