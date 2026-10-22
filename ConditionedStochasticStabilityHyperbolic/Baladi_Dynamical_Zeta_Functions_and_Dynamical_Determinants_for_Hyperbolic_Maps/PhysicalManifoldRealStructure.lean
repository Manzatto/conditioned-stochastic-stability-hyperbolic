module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldConjugation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldCoreConjugation
public import LeanShared.Analysis.EvenAngularCutoff

/-! Real weighted physical transfers have a constructed conjugation on the
actual anisotropic completion. Only ordinary regular-function conjugation,
real cutoffs and even angular symbols enter the source. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldRealStructure
open LeanShared KellerLiverani1999
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


def generatorConjugation (rows : PhysicalManifoldRowSources.Data m)
    (hcutoff : ∀ i x, conj (m.localization.cutoff i x) = m.localization.cutoff i x)
    (hangle : ∀ i ξ, (m.angle i).toFun (-ξ) = (m.angle i).toFun ξ)
    (J : Reg →L[ℝ] Reg) (hJ : ∀ v x, m.view (J v) x = star (m.view v x))
    (a : Ω) : RealOperatorConjugation (m.generator a) :=
  PhysicalManifoldConjugation.generatorConjugation m rows
    (SmoothSupportedManifoldCore.conjugate V)
    (SmoothSupportedManifoldCore.conjugate_involutive V)
    (SmoothSupportedManifoldCore.conjugate_smul V)
    (fun _ _ => rfl)
    (PhysicalManifoldCoreConjugation.norm_conjugate m.atlas m.localization m.atlas_mem V
      μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
      hcutoff hangle)
    J hJ a

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldRealStructure
