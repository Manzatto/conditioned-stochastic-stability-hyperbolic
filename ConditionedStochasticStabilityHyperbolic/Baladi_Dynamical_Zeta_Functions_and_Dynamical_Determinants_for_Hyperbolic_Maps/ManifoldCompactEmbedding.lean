module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ManifoldPhysicalCore

/-!
# Actual manifold compact weakening of anisotropic exponents

The source is the literal maximum chart norm built from the constructed
partition and the specified physical cone/leaf blocks. The source isometry,
local Fourier compactness and finite chart inclusion construct a compact
injective global map. The target has precisely the weakened exponents,
including unequal losses in the two signs. Neither a localization map nor
local/global compactness is an assumption.

Only classical finite distribution order and its pairing identity are used
here. Cross-cone norm comparison may subsequently be composed using the
already checked canonical comparison producer.
-/

@[expose] public noncomputable section

open MeasureTheory Set IsManifold
open scoped Manifold ContDiff SchwartzMap NNReal

namespace ConditionedStochasticStabilityHyperbolic.ManifoldCompactEmbedding

open LeanShared

variable {E U M AtlasIndex Core A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [AddCommGroup Core] [Module ℂ Core]
  (e : AtlasIndex → OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))
  (μ : Measure U) [μ.IsAddHaarMeasure] {L : ℝ} (hL : 0 ≤ L)
  (leaves : D.indices → A → GraphLeafNorm.GraphLeaf U E L)
  {Cplus Cminus : D.indices → Set E}
  (radial : D.indices → ConeDyadicSymbols.RadialCutoff)
  (angle : ∀ i, ConeDyadicSymbols.AngularCutoff (Cplus i) (Cminus i))
  (exponent : D.indices → Bool → ℝ)
  (bounded : ∀ i, SchwartzAmbientBlocks.SmoothCoreBounded μ hL (leaves i)
    (ConstructedManifoldLocalization.support e D i)
    (ConeDyadicSymbols.symbols (radial i) (angle i)) (exponent i))


variable {loss : D.indices → ℝ} (positive : ∀ i, 0 < loss i)
  (extra : D.indices → Bool → ℝ) (nonnegative : ∀ i s, 0 ≤ extra i s)

abbrev localCore (i : D.indices) :=
  ManifoldPhysicalCore.localBlocks e D μ hL leaves radial angle exponent bounded i

/-- The constructed physical local weakening; no local operator input. -/
def localOperator (i : D.indices) := DyadicCompletion.exactInclusion
  (localCore e D μ hL leaves radial angle exponent bounded i)
  (loss i) (positive i) (extra i) (nonnegative i)

abbrev strongCore := ManifoldPhysicalCore.compactSourceCore
  e D he functions smooth μ hL leaves radial angle exponent bounded

/-- The weak global norm uses the same genuine localizations and the actual
weakened physical block weights. -/
def weakCore := FiniteChartCompletion.weakCore
  (localOperator e D μ hL leaves radial angle exponent bounded positive extra nonnegative)
  (strongCore e D he functions smooth μ hL leaves radial angle exponent bounded)

abbrev WeakSpace := DyadicCompletion.closedCore
  (weakCore e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative)

/-- The actual manifold inclusion from the manuscript source completion. -/
def embedding :
    ManifoldPhysicalCore.Space e D he functions smooth μ hL leaves radial angle exponent bounded →L[ℂ]
    WeakSpace e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative :=
  (FiniteChartCompletion.inclusion
    (localOperator e D μ hL leaves radial angle exponent bounded positive extra nonnegative)
    (strongCore e D he functions smooth μ hL leaves radial angle exponent bounded)).comp
    (ManifoldPhysicalCore.completionEquivalence
      e D he functions smooth μ hL leaves radial angle exponent bounded).toLinearIsometry.toContinuousLinearMap

set_option maxHeartbeats 800000 in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- Smooth-core agreement is exact in the actual weak global chart norm. -/
theorem embedding_core (f : Core) :
    embedding e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative
      (DyadicCompletion.coreLift
        (ManifoldPhysicalCore.coreMap e D he functions smooth μ hL leaves radial angle exponent bounded) f) =
      DyadicCompletion.coreLift
        (weakCore e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative) f := by
  exact (congrArg
    (FiniteChartCompletion.inclusion
      (localOperator e D μ hL leaves radial angle exponent bounded positive extra nonnegative)
      (strongCore e D he functions smooth μ hL leaves radial angle exponent bounded))
    (NormCompletionEquivalence.equivalence_core
      (ManifoldPhysicalCore.coreMap e D he functions smooth μ hL leaves radial angle exponent bounded)
      (ManifoldPhysicalCore.compactSourceCore e D he functions smooth μ hL leaves radial angle exponent bounded)
      (fun f => (ManifoldPhysicalCore.compactSourceCore_norm
        e D he functions smooth μ hL leaves radial angle exponent bounded f).symm) f)).trans
    (FiniteChartCompletion.inclusion_core
      (localOperator e D μ hL leaves radial angle exponent bounded positive extra nonnegative)
      (strongCore e D he functions smooth μ hL leaves radial angle exponent bounded) f)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- These are literally the physical target blocks at exponents
`t(sign) - loss - extra(sign)` of the same localized smooth function. -/
theorem weak_block (f : Core) (i : D.indices) (j : ℕ × Bool) :
    (weakCore e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative f i).val j =
      SchwartzAmbientBlocks.weightedBlock μ hL (leaves i)
        (ConstructedManifoldLocalization.support e D i)
        (ConeDyadicSymbols.symbols (radial i) (angle i))
        (fun s => exponent i s - loss i - extra i s) j
        (ConstructedManifoldLocalization.localize e D he functions smooth i f) :=
  LocalCompactEmbedding.canonicalWeakCore_apply μ hL (leaves i)
    (ConstructedManifoldLocalization.support e D i) (radial i) (angle i) (exponent i) (bounded i)
    (positive i) (extra i) (nonnegative i) _ j

variable {Order : Type*} [Fintype Order]
  (words : D.indices → Order → List E) {K : D.indices → Set E}
  (compactK : ∀ i, IsCompact (K i)) (cutoff : D.indices → 𝓢(E, ℂ))
  (supported : ∀ i y, y ∉ K i → cutoff i y = 0)
  (one : ∀ i y, y ∈ ConstructedManifoldLocalization.support e D i → cutoff i y = 1)
  (pairing : ∀ i, DyadicCompletion.closedCore
    (localCore e D μ hL leaves radial angle exponent bounded i) →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ))
  (Corder : D.indices → ℝ) (Corder_nonneg : ∀ i, 0 ≤ Corder i)
  (orderBound : ∀ i b (f : 𝓢(E, ℂ)), (∀ x ∉ K i, f x = 0) →
    ‖pairing i b f‖ ≤ Corder i * ‖b‖ * ‖SchwartzJetSpace.jetMap (K i) (words i) f‖)
  (pairingCore : ∀ i (f : SchwartzJetSpace.supportedCore
      (ConstructedManifoldLocalization.support e D i)) (test : 𝓢(E, ℂ)),
    pairing i (DyadicCompletion.coreLift
      (localCore e D μ hL leaves radial angle exponent bounded i) f) test =
      ConeFourierBlocks.integralPairing f.val test)

set_option maxHeartbeats 800000 in
include words compactK cutoff supported one pairing Corder Corder_nonneg orderBound pairingCore in
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- The actual manifold embedding is compact and injective. The theorem's
only analytic background is the precise classical local distribution-order
bound and pairing; the compactness deduction is fully checked here. -/
theorem compact_injective :
    IsCompactOperator (embedding e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative) ∧
    Function.Injective (embedding e D he functions smooth μ hL leaves radial angle exponent bounded positive extra nonnegative) := by
  have hlocal : ∀ i, IsCompactOperator
      (localOperator e D μ hL leaves radial angle exponent bounded positive extra nonnegative i) ∧
      Function.Injective
      (localOperator e D μ hL leaves radial angle exponent bounded positive extra nonnegative i) := by
    intro i
    exact LocalCompactEmbedding.compact_injective_exactInclusion μ hL (leaves i)
      (ConstructedManifoldLocalization.support e D i) (radial i) (angle i) (exponent i) (bounded i)
      (words i) (compactK i) (cutoff i) (supported i) (one i) (pairing i)
      (Corder i) (Corder_nonneg i) (orderBound i) (pairingCore i)
      (positive i) (extra i) (nonnegative i)
  have hc := FiniteChartCompletion.inclusion_isCompact
    (localOperator e D μ hL leaves radial angle exponent bounded positive extra nonnegative)
    (strongCore e D he functions smooth μ hL leaves radial angle exponent bounded) (fun i => (hlocal i).1)
  have hi := FiniteChartCompletion.inclusion_injective
    (localOperator e D μ hL leaves radial angle exponent bounded positive extra nonnegative)
    (strongCore e D he functions smooth μ hL leaves radial angle exponent bounded) (fun i => (hlocal i).2)
  exact ⟨hc.comp_clm (ManifoldPhysicalCore.completionEquivalence
    e D he functions smooth μ hL leaves radial angle exponent bounded).toLinearIsometry.toContinuousLinearMap,
    hi.comp (ManifoldPhysicalCore.completionEquivalence
      e D he functions smooth μ hL leaves radial angle exponent bounded).injective⟩

end ConditionedStochasticStabilityHyperbolic.ManifoldCompactEmbedding
