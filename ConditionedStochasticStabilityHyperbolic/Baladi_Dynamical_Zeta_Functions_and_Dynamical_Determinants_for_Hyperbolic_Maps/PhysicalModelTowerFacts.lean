module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelWeakTower
meta import Lean.LibrarySuggestions.Basic

/-! The global inclusions of a physical model are injective (each local exact
weakening is), and an inclusion that is the identity on the smooth core has
dense range. The intermediate inclusion gives, as the weak one does, a tower
inclusion `m.StrongSpace → n.StrongSpace` once the intermediate core norms of
`m` are the strong core norms of `n`. -/
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelTowerFacts"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelTowerFacts
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelWeakTower

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
  (m n : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

theorem inclusionW_injective : Function.Injective m.inclusionW :=
  (FiniteChartCompletion.inclusion_injective
    (ManifoldCompactEmbedding.localOperator m.atlas m.localization μ m.slope_nonnegative m.leaves
      m.radial m.angle m.exponent m.boundedBlocks m.lossW_positive m.extraW m.extraW_nonnegative)
    (ManifoldCompactEmbedding.strongCore m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
      m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks)
    (fun _ => exactInclusion_injective _ _ _ _ _)).comp
    (ManifoldPhysicalCore.completionEquivalence m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
      m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks).injective

theorem inclusionH_injective : Function.Injective m.inclusionH :=
  (FiniteChartCompletion.inclusion_injective
    (ManifoldCompactEmbedding.localOperator m.atlas m.localization μ m.slope_nonnegative m.leaves
      m.radial m.angle m.exponent m.boundedBlocks m.lossH_positive m.extraH m.extraH_nonnegative)
    (ManifoldCompactEmbedding.strongCore m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
      m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks)
    (fun _ => exactInclusion_injective _ _ _ _ _)).comp
    (ManifoldPhysicalCore.completionEquivalence m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
      m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks).injective

theorem inclusionH_isCompact
    (local_compact : ∀ i, IsCompactOperator (exactInclusion (m.localBlocks i) (m.lossH i)
      (m.lossH_positive i) (m.extraH i) (m.extraH_nonnegative i))) :
    IsCompactOperator m.inclusionH :=
  (FiniteChartCompletion.inclusion_isCompact
    (ManifoldCompactEmbedding.localOperator m.atlas m.localization μ m.slope_nonnegative m.leaves
      m.radial m.angle m.exponent m.boundedBlocks m.lossH_positive m.extraH m.extraH_nonnegative)
    (ManifoldCompactEmbedding.strongCore m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
      m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks)
    local_compact).comp_clm
    (ManifoldPhysicalCore.completionEquivalence m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) μ
      m.slope_nonnegative m.leaves m.radial m.angle m.exponent
      m.boundedBlocks).toLinearIsometry.toContinuousLinearMap

theorem inclusionH_core (c : Core (E := E) V) :
    m.inclusionH (coreLift m.qa c) = coreLift m.qH c :=
  ManifoldCompactEmbedding.embedding_core m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossH_positive m.extraH m.extraH_nonnegative c

/-- An operator into `n.StrongSpace` that is the identity on the smooth core
has dense range. -/
theorem denseRange_of_core (j : m.StrongSpace →L[ℂ] n.StrongSpace)
    (hcore : ∀ c, j (coreLift m.qa c) = coreLift n.qa c) : DenseRange j := by
  refine Dense.mono ?_ (coreLift_dense n.qa)
  rintro _ ⟨c, rfl⟩
  exact ⟨coreLift m.qa c, hcore c⟩

/-- Two operators that agree with the identity on the smooth core are equal. -/
theorem eq_of_core (j k : m.StrongSpace →L[ℂ] n.StrongSpace)
    (hj : ∀ c, j (coreLift m.qa c) = coreLift n.qa c)
    (hk : ∀ c, k (coreLift m.qa c) = coreLift n.qa c) : j = k := by
  apply ContinuousLinearMap.ext
  intro x
  exact (coreLift_dense m.qa).induction_on (p := fun x => j x = k x) x
    (isClosed_eq j.continuous k.continuous) fun c => (hj c).trans (hk c).symm

section Weak
variable (hnorm : ∀ c, ‖m.qW c‖ = ‖n.qa c‖)

theorem towerInclusion_injective : Function.Injective (towerInclusion m n hnorm) :=
  (NormCompletionEquivalence.equivalence m.qW n.qa hnorm).injective.comp (inclusionW_injective m)

theorem towerInclusion_denseRange : DenseRange (towerInclusion m n hnorm) :=
  denseRange_of_core m n _ (towerInclusion_core m n hnorm)

end Weak

section Intermediate
variable (hnorm : ∀ c, ‖m.qH c‖ = ‖n.qa c‖)

/-- The intermediate inclusion of `m`, read in the strong completion of `n`. -/
def towerInclusionH : m.StrongSpace →L[ℂ] n.StrongSpace :=
  (NormCompletionEquivalence.equivalence m.qH n.qa hnorm).toLinearIsometry.toContinuousLinearMap.comp
    m.inclusionH

theorem towerInclusionH_core (c : Core (E := E) V) :
    towerInclusionH m n hnorm (coreLift m.qa c) = coreLift n.qa c :=
  (congrArg (NormCompletionEquivalence.equivalence m.qH n.qa hnorm) (inclusionH_core m c)).trans
    (NormCompletionEquivalence.equivalence_core _ _ _ c)

theorem towerInclusionH_compact (compact : IsCompactOperator m.inclusionH) :
    IsCompactOperator (towerInclusionH m n hnorm) :=
  compact.clm_comp _

theorem towerInclusionH_injective : Function.Injective (towerInclusionH m n hnorm) :=
  (NormCompletionEquivalence.equivalence m.qH n.qa hnorm).injective.comp (inclusionH_injective m)

theorem towerInclusionH_denseRange : DenseRange (towerInclusionH m n hnorm) :=
  denseRange_of_core m n _ (towerInclusionH_core m n hnorm)

theorem towerInclusionH_norm (x : m.StrongSpace) :
    ‖towerInclusionH m n hnorm x‖ = ‖m.inclusionH x‖ :=
  LinearIsometryEquiv.norm_map _ _

end Intermediate

end ConditionedStochasticStabilityHyperbolic.PhysicalModelTowerFacts
