module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelPairIdentification
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeProductIdentification
meta import Lean.LibrarySuggestions.Basic

/-! The identified pair for the strong multipliers by smooth real functions, with the product
identity of the intermediate generator stated through the native leading records, so concrete
carrier statements only instantiate generic propositions. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelPairNativeIdentification"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter Topology IsManifold MeasureTheory
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedPair
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelWeakTower
open PhysicalModelTowerFacts KellerLiverani1999 PhysicalModelHorizonIdentities

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m₀ m₁ m₂ : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  [MetricSpace Ω] {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
  [OpensMeasurableSpace Z] [SecondCountableTopology Z]
  (law : ℝ≥0 → Measure Z) (hprob : ∀ ε, IsProbabilityMeasure (law ε)) (G : ℝ≥0 → Z → Ω)
  (R ρ₀ ρ₁ weak₀ weak₁ : ℝ)

/-- The normed group of the strong space, as synthesized for the generic pair statements; used as
a local instance by concrete carriers so that their synthesized instances agree syntactically. -/
@[instance_reducible] def pairStrongNormed : NormedAddCommGroup m₀.StrongSpace := inferInstance

/-- The complex normed structure of the strong space, as synthesized for the generic pair
statements. -/
@[instance_reducible] def pairStrongScalar : NormedSpace ℂ m₀.StrongSpace := inferInstance

/-- Completeness of the strong space, as synthesized for the generic pair statements. -/
theorem pairStrongComplete : CompleteSpace m₀.StrongSpace := inferInstance

/-- The identified pair for the strong multipliers by smooth real functions. -/
def NativePairIdentified (lam : ℝ) (value : {ψ : M → ℝ // ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ} → ℝ) :
    Prop :=
  PairIdentifiedConclusion m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁ lam
    (fun ψ : {ψ : M → ℝ // ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ} => strongMultiplier m₁ ψ.1 ψ.2) value

/-- The identified pair from leading records of both raw generators and the spectral product
identity of the intermediate one. -/
theorem PairStatement.identified_native
    (h : PairStatement m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁)
    (a₀ : Ω) (G0 : ∀ z, G 0 z = a₀) (lam : ℝ) (gap₀ : ρ₀ < lam) (gap₁ : ρ₁ < lam)
    (lead₀ : LeadingFrom m₀ a₀ lam m₂.StrongSpace) (lead₁ : LeadingFrom m₁ a₀ lam m₂.StrongSpace)
    (value : {ψ : M → ℝ // ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ} → ℝ)
    (identified : ∀ (ψ : {ψ : M → ℝ // ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ}) (d : LeadingRecord m₁ a₀),
      d.rate = lam → productValue m₁ d ψ.1 ψ.2 = value ψ) :
    NativePairIdentified m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁ lam value := by
  have t0 := PairStatement.identified m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁ h a₀ G0 lam gap₀ gap₁
    (Ψ := {ψ : M → ℝ // ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ})
  have t1 := t0 lead₀
  have t2 := t1 lead₁
  have t3 := t2 (fun ψ => strongMultiplier m₁ ψ.1 ψ.2) value
  have t4 := t3 (fun ψ d hd => identified ψ d hd)
  exact t4

end ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedPair
