module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldConjugation
public import ConditionedStochasticStabilityHyperbolic.Spectral.RegularActionConjugation
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedConjugation

/-! Even-symbol physical norm conjugation and ordinary little-Hölder
conjugation construct actual analytic real-operator structure. All completed
conjugation and actual weighted-transfer commutation are deductions. -/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedConjugation
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


set_option synthInstance.maxHeartbeats 400000 in
def actual_conjugation
    {Noise W : Type*} [MeasurableSpace Noise]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
    (noise : ℝ≥0 → Noise → Ω)
    (i : m.StrongSpace →L[ℂ] W) (R : ℝ)
    (inputs : ActualAnnealedInputs law (fun _ => inferInstance) i R)
    (generator_eq : ∀ ε z, inputs.generator ε z = m.generator (noise ε z))
    (ε : ℝ≥0) : RealOperatorConjugation (inputs.operator ε) := by
  let d := PhysicalManifoldConjugation.coreData m J0 hJ0 hJ0smul hnorm
  let JC := CoreConjugation.extension (coreLift m.qa) d
  have commute (δ : ℝ≥0) (z : Noise) (v : m.StrongSpace) :
      inputs.generator δ z (JC v) = JC (inputs.generator δ z v) := by
    have hreg (c : PhysicalManifoldModel.Core (E := E) V) :
        J (m.regularCore c) = m.regularCore (J0 c) := by
      apply m.view_injective
      funext x
      rw [hJ, m.view_core, m.view_core, hJ0functions]
    let a := noise δ z
    let action := regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      m.maps m.weight m.coreRegular a
    have hP := operator_core m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      m.realize m.maps m.weight m.coreRegular rows.strongBound (rows.produced m).strong a
    have ha (c : PhysicalManifoldModel.Core (E := E) V) : action (J0 c) = J (action c) :=
      CoreConjugation.regular_action_commutes (SmoothSupportedManifoldCore.functions V)
        m.view m.view_injective m.maps m.weight m.coreRegular J0 J hJ0functions hJ a c
    let cg := CoreConjugation.operator (coreLift m.qa) (coreLift_dense m.qa) d
      (m.generator a) m.regularCore m.regularCore_dense m.realize m.realize_core J hreg action hP ha
    have hJC : cg.conjugate = JC := rfl
    have hc := cg.commute v
    have hc' : m.generator a (JC v) = JC (m.generator a v) :=
      (congrArg (fun f : m.StrongSpace → m.StrongSpace => m.generator a (f v)) hJC).symm.trans
        (hc.trans (congrFun hJC (m.generator a v)))
    exact (congrArg (fun P : m.StrongSpace →L[ℂ] m.StrongSpace => P (JC v)) (generator_eq δ z)).trans
      (hc'.trans (congrArg (fun P : m.StrongSpace →L[ℂ] m.StrongSpace => JC (P v)) (generator_eq δ z)).symm)
  have produced := inputs.conjugation_of_generators JC
    (CoreConjugation.extension_involutive (coreLift m.qa) (coreLift_dense m.qa) d)
    (CoreConjugation.extension_smul (coreLift m.qa) (coreLift_dense m.qa) d) commute ε
  exact produced


end ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedConjugation
