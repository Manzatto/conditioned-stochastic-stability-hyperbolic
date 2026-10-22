module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel

/-! The literal completed maximum chart norm has jointly faithful local
completed coordinates, constructed by dense-core closure. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared DyadicCompletion CompletedChartPairTransfer FiniteRegularTransferRealization

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


@[expose] def localProjection (i : m.localization.indices) : m.StrongSpace→L[ℂ]
    DyadicCompletion.BlockSpace (F:=GraphLeafNorm.AmbientFamilySpace μ (m.leaves i)) (S:=Bool) :=
  (ContinuousLinearMap.proj i).comp (closedCore m.qa).subtypeL

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem localProjection_mem (i : m.localization.indices) (z : m.StrongSpace) :
    m.localProjection i z∈closedCore (m.localBlocks i) := by
  refine (coreLift_dense m.qa).induction_on z
    (((m.localBlocks i).range.isClosed_topologicalClosure).preimage (m.localProjection i).continuous) ?_
  intro c
  exact (m.localBlocks i).range.le_topologicalClosure ⟨_,rfl⟩

@[expose] def localCompletion (i : m.localization.indices) :
    m.StrongSpace→L[ℂ]closedCore (m.localBlocks i) :=
  (m.localProjection i).codRestrict (closedCore (m.localBlocks i)) (m.localProjection_mem i)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem localCompletion_core (i : m.localization.indices) (c : Core (E:=E) V) :
    m.localCompletion i (coreLift m.qa c)=coreLift (m.localBlocks i)
      (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i c) := by
  apply Subtype.ext
  rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ i, CompleteSpace (LocalReg i)] in
theorem localCompletion_jointly_injective {z w : m.StrongSpace}
    (equal : ∀ i,m.localCompletion i z=m.localCompletion i w) : z=w := by
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (equal i)

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
