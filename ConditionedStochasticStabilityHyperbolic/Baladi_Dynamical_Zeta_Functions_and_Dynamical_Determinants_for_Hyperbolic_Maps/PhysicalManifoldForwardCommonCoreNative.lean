module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldSupportedCore
public import ConditionedStochasticStabilityHyperbolic.Spectral.RawRegularAverageRealizations
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalytic
meta import Lean.LibrarySuggestions.Basic

/-! Native companion (one-step core bound instead of row sources).
 The literal manifold regular action constructs the forward common core
for Appendix A.2. Both completed intertwining identities are outputs of
actual averaging and the killed-kernel formula, never source assumptions. -/
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalManifoldForwardCommonCoreNative"

public noncomputable section
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldForwardCommonCoreNative
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open SmoothSupportedManifoldCore KellerLiverani1999

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


variable [MetricSpace Ω]

omit [SecondCountableTopology M] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] in
theorem exists_forward
    {Lrows : ℝ} (analytic : PhysicalModelAnalytic.AnalyticBound m Lrows) (n : PhysicalManifoldNoiseSources.Data m)
    {Noise W : Type*} [TopologicalSpace Noise] [MeasurableSpace Noise]
    [OpensMeasurableSpace Noise] [SecondCountableTopology Noise]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
    (noise : ℝ≥0 → Noise → Ω) (hnoise : ∀ ε, Continuous (noise ε))
    (j : m.StrongSpace →L[ℂ] W) (R : ℝ)
    (inputs : ActualAnnealedInputs law (fun _ => inferInstance) j R)
    (hgenerator : ∀ ε z, inputs.generator ε z = m.generator (noise ε z))
    (K : Set M) [CompactSpace K]
    (uniformConstant : ℝ)
    (uniformBound : ∀ c, ‖physicalCore V K c‖ ≤ uniformConstant * ‖m.regularCore c‖)
    (hVK : V ⊆ K) (hK : MeasurableSet K) (ε : ℝ≥0)
    (hF : Measurable (fun z : M × Noise => m.maps (noise ε z.2) z.1))
    (wc : K → ℝ) (hwc : Measurable wc) (hwc0 : ∀ x, 0 ≤ wc x)
    (hR : 0 < R) (hwcR : ∀ x, wc x ≤ R)
    (hweight : ∀ x : K, m.weight x.val = wc x)
    (sf : HasStrongFellerKernel (RestrictedNoise.chain (law ε)
      (fun z : M × Noise => m.maps (noise ε z.2) z.1) hF K hK wc hwc R hR hwcR)) :
    ∃ forward : Reg →L[ℂ] Reg,
      m.realize.comp forward = ((R : ℂ) • inputs.operator ε).comp m.realize ∧
      (physicalRealization V K m.regularCore).comp forward =
        ((R : ℂ) • ComplexStrongFeller.transferOperator
          (RestrictedNoise.chain (law ε)
            (fun z : M × Noise => m.maps (noise ε z.2) z.1) hF K hK wc hwc R hR hwcR) sf).comp
          (physicalRealization V K m.regularCore) := by
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
  have hevalCore : ∀ x c, m.evaluate x (m.regularCore c) = functions V c x := by
    intro x c
    rw [m.evaluation, m.view_core]
  have hphysical : ∀ v (x : K), physicalRealization V K m.regularCore v x = m.view v x.val := by
    intro v x
    rw [physicalRealization_value V K m.regularCore m.regularCore_dense
      uniformConstant uniformBound m.evaluate hevalCore, m.evaluation]
  have hzero : ∀ v x, x ∉ K → m.view v x = 0 := by
    intro v x hx
    rw [← m.evaluation]
    exact evaluate_zero_outside_live V K m.regularCore m.regularCore_dense
      m.evaluate hevalCore hVK v x hx
  let forward := InvariantFiniteRegularTransfer.average m.view m.view_injective maps
    m.weight invariant bound hbound (law ε) hmeas (le_max_left 0 _)
  have hp := ActualInvariantCoreAverage.normalized_realizations (law ε) m.view m.view_injective
    maps m.weight invariant bound (le_max_left 0 _) hbound hmeas m.regularCore
    m.regularCore_dense m.realize (inputs.generator ε) (inputs.measurable ε)
    inputs.operatorBound (inputs.generator_bound ε) hcore K hK hF wc hwc hwc0 R hR hwcR
    hweight sf (physicalRealization V K m.regularCore) hphysical hzero
  have hP := inputs.operator_eq_actual_average ε (inputs.generator ε)
    (inputs.measurable ε) inputs.operatorBound (inputs.generator_bound ε) (fun _ => rfl)
  have raw := RawRegularAverageRealizations.cancel_normalization
    (Reg := Reg) (A := m.StrongSpace) (F := (K →ᵇ ℂ)) m.realize
    (physicalRealization V K m.regularCore) forward (inputs.operator ε)
    (AnnealedOperatorBounds.pointwiseAnnealed (law ε) (inputs.generator ε)
      (inputs.measurable ε) inputs.operatorBound (inputs.generator_bound ε))
    (ComplexStrongFeller.transferOperator (𝕜 := ℂ)
      (RestrictedNoise.chain (law ε)
        (fun z : M × Noise => maps z.2 z.1) hF K hK wc hwc R hR hwcR) sf)
    R hR hP (by exact hp.1) (by exact hp.2)
  exact Exists.intro forward raw

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldForwardCommonCoreNative
