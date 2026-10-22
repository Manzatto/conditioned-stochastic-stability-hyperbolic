module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarriers
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldWeakening
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNormInstances
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelIntermediateCarriers

@[expose] public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared DyadicCompletion
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

namespace Data
variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

@[instance_reducible] def nativeStrongUniform : UniformSpace m.StrongSpace :=
  m.strongSeminormedParent.toUniformSpace

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem nativeStrongComplete :
    letI : UniformSpace m.StrongSpace := m.nativeStrongUniform
    CompleteSpace m.StrongSpace := by
  infer_instance

@[instance_reducible] def nativeWeakNormed : NormedAddCommGroup (closedCore (m.loweredCore m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)) := inferInstance

@[instance_reducible] def nativeWeakSemi : SeminormedAddCommGroup (closedCore (m.loweredCore m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)) :=
  m.nativeWeakNormed.toSeminormedAddCommGroup

@[instance_reducible] def nativeWeakScalar :
    letI := m.nativeWeakSemi
    NormedSpace ℂ (closedCore (m.loweredCore m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)) := by
  letI := m.nativeWeakSemi
  infer_instance

@[instance_reducible] def nativeWeakUniform : UniformSpace (closedCore (m.loweredCore m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)) :=
  m.nativeWeakSemi.toUniformSpace

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem nativeWeakComplete :
    letI : UniformSpace (closedCore (m.loweredCore m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)) := m.nativeWeakUniform
    CompleteSpace (closedCore (m.loweredCore m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)) := by
  infer_instance

@[instance_reducible] def nativeIntermediateNormed : NormedAddCommGroup (closedCore (m.loweredCore m.lossH m.lossH_positive m.extraH m.extraH_nonnegative)) := inferInstance

@[instance_reducible] def nativeIntermediateSemi : SeminormedAddCommGroup (closedCore (m.loweredCore m.lossH m.lossH_positive m.extraH m.extraH_nonnegative)) :=
  m.nativeIntermediateNormed.toSeminormedAddCommGroup

@[instance_reducible] def nativeIntermediateScalar :
    letI := m.nativeIntermediateSemi
    NormedSpace ℂ (closedCore (m.loweredCore m.lossH m.lossH_positive m.extraH m.extraH_nonnegative)) := by
  letI := m.nativeIntermediateSemi
  infer_instance

@[instance_reducible] def nativeIntermediateUniform : UniformSpace (closedCore (m.loweredCore m.lossH m.lossH_positive m.extraH m.extraH_nonnegative)) :=
  m.nativeIntermediateSemi.toUniformSpace

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem nativeIntermediateComplete :
    letI : UniformSpace (closedCore (m.loweredCore m.lossH m.lossH_positive m.extraH m.extraH_nonnegative)) := m.nativeIntermediateUniform
    CompleteSpace (closedCore (m.loweredCore m.lossH m.lossH_positive m.extraH m.extraH_nonnegative)) := by
  infer_instance

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
