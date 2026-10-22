module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelProductIdentification
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelFullTestDistribution
meta import Lean.LibrarySuggestions.Basic

/-! The spectral product identification with the native full-test distribution constructed while the
model remains abstract. The distribution, its core identity, the bounded test view and the
constant test are built here, so a concrete carrier only supplies its own regular realization
and bounds. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelNativeProductIdentification"

public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Finset Filter Real Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelHorizonIdentities
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelAnalytic
  PhysicalModelNativeCoefficients PhysicalModelNativeRadiusUpper KellerLiverani1999
  HyperbolicBasicSet ThermodynamicDefinitions FractionalManifoldRegularity

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]

/-- A deterministic leading record of the generator at the parameter `a`. -/
abbrev LeadingRecord (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ) (a : Ω) :=
  DeterministicLeading (m.generator a)

/-- The spectral product `Re m(M_ψ v)` of a leading record against the multiplier by `ψ`. -/
@[expose] def productValue (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ) {a : Ω} (d : LeadingRecord m a) (ψ : M → ℝ)
    (hψ : ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ) : ℝ :=
  (d.mean (strongMultiplier m ψ hψ d.vector)).re

/-- Every two-norm estimate of the generator at `a` against a compact operator into `W` with
essential rate below `lam` yields a leading record at the rate `lam`. -/
@[expose] def LeadingFrom (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ) (a : Ω) (lam : ℝ) (W : Type*)
    [NormedAddCommGroup W] [NormedSpace ℂ W] : Prop :=
  ∀ (i : m.StrongSpace →L[ℂ] W), IsCompactOperator i → ∀ α R C D : ℝ, 0 ≤ α → 0 ≤ R → 0 ≤ C →
    0 ≤ D → (∀ n x, ‖((m.generator a) ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖) → α < lam →
    ∃ d : LeadingRecord m a, d.rate = lam

set_option maxHeartbeats 4000000 in
/-- The spectral product functional is the equilibrium integral, with the native distribution. -/
theorem native_product_identification
    (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
      (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
    (refData : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (localBound : PhysicalModelFullTestPairing.LocalPairing m 1)
    (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
    (ψ : M → ℝ) (hψ : ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ) (CR CA : ℝ)
    (regularBound : ∀ c, ‖m.regularCore (coreMultiplier ψ hψ c)‖ ≤ CR * ‖m.regularCore c‖)
    (analyticBound : ∀ c, ‖coreLift m.qa (coreMultiplier ψ hψ c)‖ ≤ CA * ‖coreLift m.qa c‖)
    {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (seed : Reg)
    (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) (mapCont : Continuous (m.maps a))
    (weightCont : Continuous m.weight) (weightNonneg : ∀ x, 0 ≤ m.weight x)
    (d : LeadingRecord m a) (P0 : ℝ) (hrate : d.rate = exp P0)
    {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V) (hT : (T : M → M) = m.maps a)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm) (mixing : MixingOn T Λ)
    (weightRegular : Regular (E := E) (F := ℝ) q m.weight)
    (weightPos : ∀ x ∈ Λ, 0 < m.weight x)
    (weightSupport : Function.support m.weight ⊆ closure V)
    (hP0 : pressure T (bd.hyperbolic.potential m.weight) Λ = (P0 : EReal))
    (η : ProbabilityMeasure M) (hη : IsEquilibriumState T (bd.hyperbolic.potential m.weight) Λ η)
    (unique : ∀ μ, IsEquilibriumState T (bd.hyperbolic.potential m.weight) Λ μ → μ = η) :
    productValue m d ψ hψ = ∫ x, ψ x ∂(η : Measure M) := by
  have : IsFiniteMeasure (refData.measure volume) := inferInstance
  let oneCore : SmoothSupportedManifoldCore.core (E := E) (univ : Set M) :=
    ⟨fun _ => 1, contMDiff_const, subset_univ _⟩
  let testView : NativeFullHolderTests.Full (E := E) (M := M) 1 le_rfl → M →ᵇ ℂ := fun t =>
    BoundedContinuousFunction.mkOfCompact
      ⟨NativeFullHolderTests.view 1 le_rfl t,
        PhysicalModelFullTestDistribution.view_continuous (E := E) le_rfl t⟩
  exact product_identification m (refData.measure volume)
    (PhysicalModelFullTestDistribution.aFull m refData one_pos le_rfl localBound) testView
    (fun c t => PhysicalModelFullTestDistribution.aFull_core m refData one_pos le_rfl
      localBound c t)
    physReg hphys (NativeFullHolderTests.core 1 le_rfl oneCore) (fun _ => rfl) ψ hψ CR CA
    regularBound analyticBound bound a seed hseed mapCont weightCont weightNonneg d P0 hrate
    bd hT forward inverse regularity weightOrder forwardRegular inverseRegular mixing
    weightRegular weightPos weightSupport hP0 refData volume rfl η hη unique

end ConditionedStochasticStabilityHyperbolic.PhysicalModelHorizonIdentities
