module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldRowSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.RegularActionConjugation
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedConjugation

/-! Even-symbol physical norm conjugation and ordinary little-Hölder
conjugation construct actual analytic real-operator structure. All completed
conjugation and actual weighted-transfer commutation are deductions. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldConjugation
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open KellerLiverani1999

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

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

variable (rows : PhysicalManifoldRowSources.Data m)
    (J0 : PhysicalManifoldModel.Core (E := E) V →ₗ[ℝ] PhysicalManifoldModel.Core (E := E) V)
    (hJ0 : Function.Involutive J0)
    (hJ0smul : ∀ (z : ℂ) c, J0 (z • c) = star z • J0 c)
    (hJ0functions : ∀ c x, SmoothSupportedManifoldCore.functions V (J0 c) x =
      star (SmoothSupportedManifoldCore.functions V c x))
    (hnorm : ∀ c, ‖m.qa (J0 c)‖ = ‖m.qa c‖)
    (J : Reg →L[ℝ] Reg)
    (hJ : ∀ v x, m.view (J v) x = star (m.view v x))

@[expose] def coreData : CoreConjugation.CoreData (coreLift m.qa) where
  conjugate := J0
  involutive := hJ0
  smul := hJ0smul
  norm := hnorm

include hJ0functions hJ in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
private theorem regularCore_conjugation (c : PhysicalManifoldModel.Core (E := E) V) :
    J (m.regularCore c) = m.regularCore (J0 c) := by
  apply m.view_injective
  funext x
  rw [hJ, m.view_core, m.view_core, hJ0functions]

noncomputable def generatorConjugation (a : Ω) : RealOperatorConjugation (m.generator a) := by
  let d := coreData m J0 hJ0 hJ0smul hnorm
  apply CoreConjugation.operator (coreLift m.qa) (coreLift_dense m.qa) d
    (m.generator a) m.regularCore m.regularCore_dense m.realize m.realize_core
    J (regularCore_conjugation m J0 hJ0functions J hJ)
    (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      m.maps m.weight m.coreRegular a)
  · exact operator_core m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      m.realize m.maps m.weight m.coreRegular rows.strongBound (rows.produced m).strong a
  · intro c
    exact CoreConjugation.regular_action_commutes (SmoothSupportedManifoldCore.functions V)
      m.view m.view_injective m.maps m.weight m.coreRegular J0 J hJ0functions hJ a c

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldConjugation
