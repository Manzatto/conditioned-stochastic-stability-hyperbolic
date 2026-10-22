module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelForwardLeading
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeProductIdentification
meta import Lean.LibrarySuggestions.Basic

/-! The deterministic leading records of a forward-supported physical model as a generic
proposition. The native full-test distribution, its core identity, the bounded test view and the
constant test are constructed while the model is abstract, and the conclusion is stated through
the native leading records, so a concrete carrier only supplies its own calculus, pairing and
bounds. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelNativeForwardLeading"

public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelAnalytic PhysicalModelFullTestPairing PhysicalModelNativeCoefficients
  HyperbolicBasicSet FractionalManifoldRegularity ThermodynamicDefinitions
  PhysicalModelHorizonIdentities

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

set_option maxHeartbeats 3200000 in
/-- Leading records of a forward-supported model at the pressure rate, with the native
distribution. -/
theorem native_leading_forward (lc : LocalCalculus m)
    (refData : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (localBound : LocalPairing m 1) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
    (β : m.localization.indices → M → ℝ)
    (hβ : ∀ j x, m.localization.cutoff j x = (β j x : ℂ))
    (hβs : ∀ j, ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ (β j)) (openV : IsOpen V)
    {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V)
    (hT : (T : M → M) = m.maps a)
    (forwardSupport : (T : M → M) '' tsupport m.weight ⊆ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) (r : ℝ) (hr : 1 < r)
    (regular : Regular (E := E) (F := E) r T) (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (mixing : MixingOn T Λ)
    (weightCont : Continuous m.weight) (weightNonneg : ∀ x, 0 ≤ m.weight x)
    (weightPos : ∀ x ∈ Λ, 0 < m.weight x) (weightSupport : ∀ x, m.weight x ≠ 0 → x ∈ closure V)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (weightRegular : Regular (E := E) (F := ℝ) q m.weight)
    (P0 : ℝ) (hP0 : pressure T (bd.hyperbolic.potential m.weight) Λ = (P0 : EReal))
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] :
    LeadingFrom m a (Real.exp P0) W := by
  intro i hi α R C D hα hR' hC hD twoNorm gap
  let oneCore : SmoothSupportedManifoldCore.core (E := E) (univ : Set M) :=
    ⟨fun _ => 1, contMDiff_const, subset_univ _⟩
  have key := spectral_leading_forward m one_pos le_rfl lc localBound bound a strong remainder hs
    hR estimate physReg hphys β hβ hβs openV bd hT forwardSupport forward inverse r hr regular
    inverseRegular mixing weightCont weightNonneg weightPos weightSupport q hq0 hq1 weightRegular
    P0 hP0 i hi α R C D hα hR' hC hD twoNorm gap refData volume
    (PhysicalModelFullTestDistribution.aFull m refData one_pos le_rfl localBound)
    (fun t => BoundedContinuousFunction.mkOfCompact
      ⟨NativeFullHolderTests.view 1 le_rfl t,
        PhysicalModelFullTestDistribution.view_continuous (E := E) le_rfl t⟩)
    (fun c t => PhysicalModelFullTestDistribution.aFull_core m refData one_pos le_rfl
      localBound c t)
    (PhysicalModelFullTestDistribution.aFull_injective m refData one_pos le_rfl localBound)
    (NativeFullHolderTests.core 1 le_rfl oneCore) (fun _ => rfl)
  exact key

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
