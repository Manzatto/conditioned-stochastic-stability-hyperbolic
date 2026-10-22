module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.CrossConeCompactEmbedding
public import LeanShared.Analysis.FiniteChartCompletion

/-!
# Finite chart assembly of proved physical local compact embeddings

Each local datum contains the actual target physical cone blocks and only the
explicit classical/core/distribution inputs to the proved cross-cone producer. The source core map may itself be instantiated by physical blocks for another
cone and leaf family. Compactness and injectivity are derived locally and then
globally; neither is a field of the local data.

Explicit localization maps send a common global smooth core to the supported
local Schwartz cores. The global spaces are the actual closed ranges of their
finite chart maps, with the exact maximum chart norms. Their constructed map
agrees with the same localized smooth functions in the literal weak blocks.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction NNReal

namespace ConditionedStochasticStabilityHyperbolic.GlobalCompactEmbedding

open LeanShared

variable {E U A I Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [Fintype I]
  [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)

variable {Chart Core : Type*} [Fintype Chart] [AddCommGroup Core] [Module ℂ Core]
  {BPrime : Chart → Type*} [∀ i, NormedAddCommGroup (BPrime i)] [∀ i, NormedSpace ℂ (BPrime i)]
  (leaves : Chart → A → GraphLeafNorm.GraphLeaf U E J) (D : Chart → Set E)
  {Cplus Cminus : Chart → Set E} (radial : Chart → ConeDyadicSymbols.RadialCutoff)
  (angle : ∀ i, ConeDyadicSymbols.AngularCutoff (Cplus i) (Cminus i))
  (exponent : Chart → Bool → ℝ)
  (bounded : ∀ i, SchwartzAmbientBlocks.SmoothCoreBounded μ hJ (leaves i) (D i)
    (ConeDyadicSymbols.symbols (radial i) (angle i)) (exponent i))
  (sourceCore : ∀ i, SchwartzJetSpace.supportedCore (D i) →ₗ[ℂ] BPrime i)
  {loss : Chart → ℝ} (loss_pos : ∀ i, 0 < loss i)
  (extraLoss : Chart → Bool → ℝ) (extraLoss_nonneg : ∀ i s, 0 ≤ extraLoss i s)

abbrev targetCore (i : Chart) :=
  LocalCompactEmbedding.coreMap μ hJ (leaves i) (D i) (radial i) (angle i) (exponent i) (bounded i)

abbrev localWeakCore (i : Chart) :=
  DyadicCompletion.finalCore (targetCore μ hJ leaves D radial angle exponent bounded i)
    (loss i) (loss_pos i) (extraLoss i) (extraLoss_nonneg i)

/-- Actual physical cross-cone local maps, before supplying their cited estimates. -/
def localMaps (i : Chart) : DyadicCompletion.closedCore (sourceCore i) →L[ℂ]
    DyadicCompletion.closedCore (localWeakCore μ hJ leaves D radial angle exponent bounded loss_pos extraLoss extraLoss_nonneg i) :=
  CrossConeCompactEmbedding.embedding μ hJ (leaves i) (D i) (radial i) (angle i) (exponent i) (bounded i)
    (sourceCore i) (loss_pos i) (extraLoss i) (extraLoss_nonneg i)

variable (localize : ∀ i, Core →ₗ[ℂ] SchwartzJetSpace.supportedCore (D i))

/-- Actual strong chart coordinates of the common localized smooth core. -/
def strongChartMap : Core →ₗ[ℂ] (∀ i, DyadicCompletion.closedCore (sourceCore i)) :=
  LinearMap.pi fun i => (DyadicCompletion.coreLift (sourceCore i)).comp (localize i)

/-- Transferred weak coordinates; `weakChartMap_apply` proves their agreement
with the literal weak physical smooth core. -/
def weakChartMap := FiniteChartCompletion.weakCore
  (localMaps μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg)
  (strongChartMap D sourceCore localize)

abbrev StrongSpace := DyadicCompletion.closedCore (strongChartMap D sourceCore localize)
abbrev WeakSpace := DyadicCompletion.closedCore
  (weakChartMap μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg localize)

/-- The global spaces carry the finite-product maximum chart norm. The map
is constructed by the finite-chart closure producer. -/
def embedding := FiniteChartCompletion.inclusion
  (localMaps μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg)
  (strongChartMap D sourceCore localize)

omit [T2Space Z] in
@[simp]
theorem embedding_core (c : Core) :
    embedding μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg localize
      (DyadicCompletion.coreLift (strongChartMap D sourceCore localize) c) =
    DyadicCompletion.coreLift
      (weakChartMap μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg localize) c :=
  FiniteChartCompletion.inclusion_core _ _ c

variable (comparisonConstant : Chart → ℝ)
  (comparison_bound : ∀ i f, ‖targetCore μ hJ leaves D radial angle exponent bounded i f‖ ≤
    comparisonConstant i * ‖sourceCore i f‖)

include comparisonConstant comparison_bound in
omit [Fintype Chart] [T2Space Z] in
@[simp]
theorem weakChartMap_apply (c : Core) (i : Chart) :
    weakChartMap μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg localize c i =
      DyadicCompletion.coreLift
        (localWeakCore μ hJ leaves D radial angle exponent bounded loss_pos extraLoss extraLoss_nonneg i)
        (localize i c) :=
  CrossConeCompactEmbedding.Canonical.embedding_core (sourceCore i)
    (targetCore μ hJ leaves D radial angle exponent bounded i)
    (loss_pos i) (extraLoss i) (extraLoss_nonneg i)
    (comparisonConstant i) (comparison_bound i) (localize i c)

variable (words : Chart → I → List E) {K : Chart → Set E}
  (compact_K : ∀ i, IsCompact (K i)) (cutoff : Chart → 𝓢(E, ℂ))
  (cutoff_supported : ∀ i y, y ∉ K i → cutoff i y = 0)
  (cutoff_one : ∀ i y, y ∈ D i → cutoff i y = 1)
  (pairing : ∀ i, DyadicCompletion.closedCore (targetCore μ hJ leaves D radial angle exponent bounded i) →ₗ[ℂ]
    (𝓢(E, ℂ) →ₗ[ℂ] ℂ))
  (orderConstant : Chart → ℝ) (orderConstant_nonneg : ∀ i, 0 ≤ orderConstant i)
  (order_bound : ∀ i b (f : 𝓢(E, ℂ)), (∀ x ∉ K i, f x = 0) →
    ‖pairing i b f‖ ≤ orderConstant i * ‖b‖ * ‖SchwartzJetSpace.jetMap (K i) (words i) f‖)
  (pairing_core : ∀ i (f : SchwartzJetSpace.supportedCore (D i)) (test : 𝓢(E, ℂ)),
    pairing i (DyadicCompletion.coreLift (targetCore μ hJ leaves D radial angle exponent bounded i) f) test =
      ConeFourierBlocks.integralPairing f.val test)
  (sourceDistribution : ∀ i, DyadicCompletion.closedCore (sourceCore i) →L[ℂ] Z)
  (targetDistribution : ∀ i,
    DyadicCompletion.closedCore (targetCore μ hJ leaves D radial angle exponent bounded i) →L[ℂ] Z)
  (distribution_core : ∀ i f, targetDistribution i
      (DyadicCompletion.coreLift (targetCore μ hJ leaves D radial angle exponent bounded i) f) =
    sourceDistribution i (DyadicCompletion.coreLift (sourceCore i) f))
  (sourceDistribution_injective : ∀ i, Function.Injective (sourceDistribution i))

include comparisonConstant comparison_bound words compact_K cutoff cutoff_supported cutoff_one pairing
  orderConstant orderConstant_nonneg order_bound pairing_core sourceDistribution targetDistribution
  distribution_core sourceDistribution_injective in
/-- Compactness and injectivity follow from the proved physical local
cross-cone construction, not from supplied local compactness fields. -/
theorem compact_injective_embedding :
    IsCompactOperator (embedding μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg localize) ∧
    Function.Injective (embedding μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg localize) := by
  have hlocal : ∀ i, IsCompactOperator
      (localMaps μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg i) ∧
      Function.Injective
      (localMaps μ hJ leaves D radial angle exponent bounded sourceCore loss_pos extraLoss extraLoss_nonneg i) := by
    intro i
    exact CrossConeCompactEmbedding.compact_injective_embedding μ hJ (leaves i) (D i)
      (radial i) (angle i) (exponent i) (bounded i) (sourceCore i)
      (comparisonConstant i) (comparison_bound i) (loss_pos i) (extraLoss i) (extraLoss_nonneg i)
      (words i) (compact_K i) (cutoff i) (cutoff_supported i) (cutoff_one i)
      (pairing i) (orderConstant i) (orderConstant_nonneg i) (order_bound i) (pairing_core i)
      (sourceDistribution i) (targetDistribution i) (distribution_core i) (sourceDistribution_injective i)
  exact ⟨FiniteChartCompletion.inclusion_isCompact _ _ (fun i => (hlocal i).1),
    FiniteChartCompletion.inclusion_injective _ _ (fun i => (hlocal i).2)⟩

end ConditionedStochasticStabilityHyperbolic.GlobalCompactEmbedding
