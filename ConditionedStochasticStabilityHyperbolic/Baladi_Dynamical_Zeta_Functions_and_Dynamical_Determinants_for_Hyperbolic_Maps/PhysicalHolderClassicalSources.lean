module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.HolderSmoothTestCoreSources
public import LeanShared.Analysis.CommonAmbientGlobalTests

/-! Ordinary cited anisotropic facts over the actual supported/full little
Hölder spaces. All regular realizations, dense cores, test inclusions and
physical compatibility identities are constructed, not source fields. -/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalHolderClassicalSources
open LeanShared DyadicCompletion SmoothSupportedManifoldCore

variable {E U M AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable (u : ℝ)
  (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)

abbrev Regular (V : Set M) := SmoothHolderTestSpaces.space u holder V
abbrev FullTest := SmoothHolderTestSpaces.space u holder (univ : Set M)

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Regular u holder V) (LocalReg := LocalReg)
    (A := A) (Ω := Ω) V S μ)
  (K : Set M) [CompactSpace K] (σ : Measure K) [IsFiniteMeasure σ]

/-- The fractional distribution embedding and ordinary smooth integral
formula, together with the cited anisotropic smooth multiplication bound.
Its classical construction requires the paper's strict fractional-order
margins; this record makes no existence assertion outside those margins. -/
structure SourceData {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (qa : core (E := E) V →ₗ[ℂ] H) where
  core_eq : m.regularCore = SmoothHolderTestSpaces.coreMap u holder V
  fullEmbedding : H →L[ℂ] (FullTest u holder →L[ℂ] ℂ)
  fullEmbedding_injective : Function.Injective fullEmbedding
  smoothPairing : ∀ c : core (E := E) V, ∀ d : core (E := E) (univ : Set M),
    fullEmbedding (qa c) (SmoothHolderTestSpaces.coreMap u holder univ d) =
      ∫ x : K, functions V c x.val * functions univ d x.val ∂σ
  analyticMultiplierBound : ∀ (ψ : M → ℂ)
      (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
    ∃ C : ℝ, ∀ c, ‖qa (multiplier V ψ hψ c)‖ ≤ C * ‖qa c‖

abbrev Data := SourceData u holder m K σ (coreLift m.qa)

namespace SourceData
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  {qa : core (E := E) V →ₗ[ℂ] H}
  (s : SourceData u holder m K σ qa)

@[expose] def globalPhysical : FullTest u holder →L[ℂ] (K →ᵇ ℂ) :=
  SmoothHolderTestSpaces.physicalOn u holder univ K

@[expose] def includeReg : Regular u holder V →L[ℂ] FullTest u holder :=
  SmoothHolderTestSpaces.includeFull u holder V

@[expose] def fullCore : core (E := E) (univ : Set M) →ₗ[ℂ] FullTest u holder :=
  SmoothHolderTestSpaces.coreMap u holder univ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] in
theorem fullCore_dense : DenseRange (fullCore u holder) :=
  SmoothHolderTestSpaces.coreMap_dense u holder univ

@[expose] def fullView : FullTest u holder →ₗ[ℂ] (M → ℂ) :=
  SmoothHolderTestSpaces.view u holder univ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] in
theorem fullView_injective : Function.Injective (fullView u holder) :=
  SmoothHolderTestSpaces.view_injective u holder univ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace K] in
theorem physical_eq (v : FullTest u holder) (x : K) :
    globalPhysical u holder K v x = fullView u holder v x.val := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] in
theorem core_continuous (c : core (E := E) (univ : Set M)) :
    Continuous (fullView u holder (fullCore u holder c)) := (smooth univ c).continuous

@[expose] def supportedEmbedding : H →L[ℂ] (Regular u holder V →L[ℂ] ℂ) :=
  (CommonAmbientGlobalTests.restriction (includeReg u holder (V := V))).comp s.fullEmbedding

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] in
private theorem include_core (d : core (E := E) V) :
    includeReg u holder (SmoothHolderTestSpaces.coreMap u holder V d) =
      fullCore u holder (SmoothHolderTestSpaces.fullCoreInclusion V d) := by
  apply SmoothHolderTestSpaces.physical_injective u holder univ
  rfl

omit [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M]
  [∀ i, CompleteSpace (LocalReg i)] [CompactSpace K] [IsFiniteMeasure σ] in
theorem supported_pairing (c d : core (E := E) V) :
    s.supportedEmbedding u holder m K σ (qa c)
      (SmoothHolderTestSpaces.coreMap u holder V d) =
      ∫ x : K, functions V c x.val * functions V d x.val ∂σ := by
  change s.fullEmbedding (qa c)
    (includeReg u holder (SmoothHolderTestSpaces.coreMap u holder V d)) = _
  rw [include_core]
  exact s.smoothPairing c (SmoothHolderTestSpaces.fullCoreInclusion V d)

@[expose] def coreData : PhysicalManifoldSupportedCore.CoreData
    (K := K) (Tests := SmoothPhysicalTests.tests (E := E) K) (σ := σ)
    m.regularCore (qa) := by
  let p := PhysicalManifoldSupportedCore.CoreData.of_holder_smooth_tests u holder V K σ
    (qa) (s.supportedEmbedding u holder m K σ)
    (supported_pairing u holder m K σ s) s.analyticMultiplierBound
  exact {
    uniformConstant := p.uniformConstant
    uniformBound := by intro c; rw [s.core_eq]; exact p.uniformBound c
    embedding := s.supportedEmbedding u holder m K σ
    smoothPairing := by intro c d; rw [s.core_eq]; exact supported_pairing u holder m K σ s c d
    test := p.test
    test_smooth := p.test_smooth
    test_live := p.test_live
    regularConstant := p.regularConstant
    analyticConstant := p.analyticConstant
    regularMultiplierBound := by intro h c; rw [s.core_eq]; exact p.regularMultiplierBound h c
    analyticMultiplierBound := p.analyticMultiplierBound }

omit [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M]
  [∀ i, CompleteSpace (LocalReg i)] [IsFiniteMeasure σ] in
include s in
theorem include_view (v : Regular u holder V) :
    globalPhysical u holder K (includeReg u holder v) = physicalRealization V K m.regularCore v := by
  apply BoundedContinuousFunction.ext
  intro x
  change SmoothHolderTestSpaces.physical u holder univ
    (SmoothHolderTestSpaces.includeFull u holder V v) x.val = _
  rw [SmoothHolderTestSpaces.include_physical]
  symm
  apply physicalRealization_value V K m.regularCore m.regularCore_dense
    (s.coreData u holder m K σ).uniformConstant (s.coreData u holder m K σ).uniformBound
    (SmoothHolderTestSpaces.evaluate u holder V)
  intro y c
  rw [s.core_eq]
  rfl

omit [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M]
  [∀ i, CompleteSpace (LocalReg i)] [CompactSpace K] [IsFiniteMeasure σ] in
include s in
theorem view_eq (v : Regular u holder V) (x : M) :
    m.view v x = SmoothHolderTestSpaces.view u holder V v x := by
  have eq : (fun f => m.evaluate x f) =
      fun f => SmoothHolderTestSpaces.evaluate u holder V x f := by
    apply m.regularCore_dense.equalizer (m.evaluate x).continuous
      (SmoothHolderTestSpaces.evaluate u holder V x).continuous
    funext c
    change m.evaluate x (m.regularCore c) =
      SmoothHolderTestSpaces.evaluate u holder V x (m.regularCore c)
    rw [m.evaluation, m.view_core, s.core_eq]
    rfl
  exact (m.evaluation x v).symm.trans (congrFun eq v)

omit [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M]
  [∀ i, CompleteSpace (LocalReg i)] [IsFiniteMeasure σ] in
theorem smoothFull (c : core (E := E) V) (d : core (E := E) (univ : Set M)) :
    s.fullEmbedding (qa c) (fullCore u holder d) =
      ∫ x : K, physicalCore V K c x * globalPhysical u holder K (fullCore u holder d) x ∂σ :=
  s.smoothPairing c d

omit [BorelSpace M] [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M]
  [∀ i, CompleteSpace (LocalReg i)] [IsFiniteMeasure σ] in
theorem smoothRestriction (c d : core (E := E) V) :
    s.fullEmbedding (qa c) (includeReg u holder (m.regularCore d)) =
      (s.coreData u holder m K σ).embedding (qa c) (m.regularCore d) := by
  rfl

end SourceData
end ConditionedStochasticStabilityHyperbolic.PhysicalHolderClassicalSources
