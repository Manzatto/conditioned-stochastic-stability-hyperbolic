module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ActualManifoldRealStructure
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalytic
meta import Lean.LibrarySuggestions.Basic

/-! Real structure of the annealed operators of a physical model from its
uniform one-step core bound: even angular
symbols, real localization cutoffs and conjugation on the ordinary regular
space give a conjugation commuting with every averaged operator. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelRealStructure"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelRealStructure
open LeanShared DyadicCompletion FiniteRegularTransferRealization KellerLiverani1999

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (hcutoff : ∀ i x, conj (m.localization.cutoff i x) = m.localization.cutoff i x)
  (hangle : ∀ i ξ, (m.angle i).toFun (-ξ) = (m.angle i).toFun ξ)
  (Jreg : Reg →L[ℝ] Reg) (hJreg : ∀ v x, m.view (Jreg v) x = star (m.view v x))
  {L : ℝ} (bound : PhysicalModelAnalytic.AnalyticBound m L)

/-- The real structure of every averaged operator of a record with the model's generators. -/
noncomputable def actualConjugation
    {Noise W : Type*} [MeasurableSpace Noise]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    {law : ℝ≥0 → Measure Noise} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : m.StrongSpace →L[ℂ] W} {scale : ℝ}
    (inputs : ActualAnnealedInputs law probability i scale)
    (noise : ℝ≥0 → Noise → Ω)
    (hgenerator : ∀ ε z, inputs.generator ε z = m.generator (noise ε z))
    (ε : ℝ≥0) : RealOperatorConjugation (inputs.operator ε) := by
  let q := coreLift m.qa
  let d := PhysicalManifoldCoreConjugation.coreData m.atlas m.localization m.atlas_mem V
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks hcutoff hangle
  let J := CoreConjugation.extension q d
  have hJcore : ∀ c, Jreg (m.regularCore c) = m.regularCore (d.conjugate c) := by
    intro c
    apply m.view_injective
    funext x
    rw [hJreg, m.view_core, m.view_core]
    rfl
  have hcomm : ∀ a x, m.generator a (J x) = J (m.generator a x) := by
    intro a x
    let real := CoreConjugation.operator q (coreLift_dense m.qa) d (m.generator a)
      m.regularCore m.regularCore_dense m.realize m.realize_core Jreg hJcore
      (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
        m.maps m.weight m.coreRegular a)
      (PhysicalModelAnalytic.generator_core m bound a)
      (fun c => CoreConjugation.regular_action_commutes
        (SmoothSupportedManifoldCore.functions V) m.view m.view_injective m.maps m.weight m.coreRegular
        d.conjugate Jreg (fun _ _ => rfl) hJreg a c)
    exact real.commute x
  apply inputs.conjugation_of_generators J
    (CoreConjugation.extension_involutive q (coreLift_dense m.qa) d)
    (CoreConjugation.extension_smul q (coreLift_dense m.qa) d)
  intro η z x
  have h₁ := congrArg (fun L : m.StrongSpace →L[ℂ] m.StrongSpace => L (J x)) (hgenerator η z)
  have h₂ := congrArg J (congrArg (fun L : m.StrongSpace →L[ℂ] m.StrongSpace => L x) (hgenerator η z))
  exact h₁.trans ((hcomm (noise η z) x).trans h₂.symm)

end ConditionedStochasticStabilityHyperbolic.PhysicalModelRealStructure
