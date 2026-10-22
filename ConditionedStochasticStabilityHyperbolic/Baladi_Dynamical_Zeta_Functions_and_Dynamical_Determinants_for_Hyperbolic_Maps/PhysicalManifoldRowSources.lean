module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModelCore
public import LeanShared.Geometry.CompletedRectangularCoreBound
public import LeanShared.Analysis.CompletedRealizationTransport
public import LeanShared.Analysis.DyadicInclusionNorm
public import LeanShared.Analysis.FiniteRegularTransferBetweenSpaces
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedCoreRows

/-!
# Local one-step chart rows on the same little-regularity core

Actual dyadic weakening is a contraction, so its ordinary regular embedding
bound follows from the strong one. The weak realization is constructed and
agrees with inclusionW∘realize by core density. Primitive row data contain no
global operator norm, weak realization, compactness, perturbation or gap.
-/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldRowSources
open LeanShared LeanShared.DyadicCompletion LeanShared.CompletedChartPairTransfer
open LeanShared.FiniteRegularTransferRealization

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*}
  [∀ k, NormedAddCommGroup (LocalReg k)] [∀ k, NormedSpace ℂ (LocalReg k)]
  [∀ k, CompleteSpace (LocalReg k)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)


omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem weakHCoreMap : CompletedChartPairTransfer.coreMap
    m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
    (SmoothSupportedManifoldCore.smooth V) m.weakLocalBlocksH = m.qH :=
  ManifoldMicrolocalWeakCore.rowWeakCore_eq m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossH_positive m.extraH m.extraH_nonnegative

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem weakWCoreMap : CompletedChartPairTransfer.coreMap
    m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
    (SmoothSupportedManifoldCore.smooth V) m.weakLocalBlocksW = m.qW :=
  ManifoldMicrolocalWeakCore.rowWeakCore_eq m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    μ m.slope_nonnegative m.leaves m.radial m.angle m.exponent m.boundedBlocks
    m.lossW_positive m.extraW m.extraW_nonnegative

/- The genuine weakening contraction supplies its ordinary embedding bound. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem weak_block_bound (k : m.localization.indices)
    (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support m.atlas m.localization k)) :
    ‖m.weakLocalBlocksW k f‖ ≤ m.blockConstant k * ‖m.localCore k f‖ := by
  exact (DyadicInclusionNorm.norm_exactInclusion_le (m.localBlocks k)
    (m.lossW k) (m.lossW_positive k) (m.extraW k) (m.extraW_nonnegative k)
    (coreLift (m.localBlocks k) f)).trans (m.blockBound k f)

def rawWeakRealize := CompletedChartPairTransfer.realization
  m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
  (SmoothSupportedManifoldCore.smooth V) m.regularCore m.regularCore_dense
  m.localCore m.localCore_dense m.coordinateConstant m.coordinateBound
  m.weakLocalBlocksW m.blockConstant (weak_block_bound m)

def weakRealize : Reg →L[ℂ] m.WeakSpace := CompletedRealizationTransport.transport
  (CompletedChartPairTransfer.coreMap m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) m.weakLocalBlocksW)
  m.qW (weakWCoreMap m) (rawWeakRealize m)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
private theorem weakRealize_core (c : PhysicalManifoldModel.Core (E := E) V) :
    weakRealize m (m.regularCore c) = coreLift m.qW c :=
  CompletedRealizationTransport.transport_core _ _ _ (rawWeakRealize m) m.regularCore
    (CompletedChartPairTransfer.realization_core m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      m.regularCore m.regularCore_dense m.localCore m.localCore_dense m.coordinateConstant m.coordinateBound
      m.weakLocalBlocksW m.blockConstant (weak_block_bound m)) c

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
private theorem weakRealize_norm (f : Reg) :
    ‖weakRealize m f‖ = ‖rawWeakRealize m f‖ :=
  CompletedRealizationTransport.norm_transport
    (CompletedChartPairTransfer.coreMap m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) m.weakLocalBlocksW)
    m.qW (weakWCoreMap m) (rawWeakRealize m) f

@[expose] def inputStrongNorm (j : m.localization.indices) (c : PhysicalManifoldModel.Core (E := E) V) : ℝ :=
  ‖m.localBlocks j (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) j c)‖

@[expose] def inputHNorm (j : m.localization.indices) (c : PhysicalManifoldModel.Core (E := E) V) : ℝ :=
  ‖m.weakLocalBlocksH j (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) j c)‖

@[expose] def inputWNorm (j : m.localization.indices) (c : PhysicalManifoldModel.Core (E := E) V) : ℝ :=
  ‖m.weakLocalBlocksW j (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) j c)‖

@[expose] def strongOutputNorm (pairMember : ∀ (a : Ω) (i j : m.localization.indices) (f : SchwartzJetSpace.supportedCore
      (ConstructedManifoldLocalization.support m.atlas m.localization j)),
    ChartPairTransfer.pair (m.atlas i) (m.atlas j) (m.localization.cutoff i)
      (m.maps a) m.weight f.val ∈ (m.localView i).range)
    (a : Ω) (i j : m.localization.indices) (c : PhysicalManifoldModel.Core (E := E) V) : ℝ :=
  ‖localRealize m.atlas m.localization m.localCore m.localBlocks i
    (RegularChartPairTransfer.localPair m.atlas m.localization (m.maps a) m.weight
      m.localView m.localView_injective (pairMember a) i j
      (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) j c))‖

@[expose] def weakOutputNorm (pairMember : ∀ (a : Ω) (i j : m.localization.indices) (f : SchwartzJetSpace.supportedCore
      (ConstructedManifoldLocalization.support m.atlas m.localization j)),
    ChartPairTransfer.pair (m.atlas i) (m.atlas j) (m.localization.cutoff i)
      (m.maps a) m.weight f.val ∈ (m.localView i).range)
    (a : Ω) (i j : m.localization.indices) (c : PhysicalManifoldModel.Core (E := E) V) : ℝ :=
  ‖localRealize m.atlas m.localization m.localCore m.weakLocalBlocksW i
    (RegularChartPairTransfer.localPair m.atlas m.localization (m.maps a) m.weight
      m.localView m.localView_injective (pairMember a) i j
      (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) j c))‖

structure Data where
  pairMember : ∀ (a : Ω) (i j : m.localization.indices) (f : SchwartzJetSpace.supportedCore
      (ConstructedManifoldLocalization.support m.atlas m.localization j)),
    ChartPairTransfer.pair (m.atlas i) (m.atlas j) (m.localization.cutoff i)
      (m.maps a) m.weight f.val ∈ (m.localView i).range
  strongConstant : m.localization.indices → m.localization.indices → ℝ
  strongConstant_nonnegative : ∀ i j, 0 ≤ strongConstant i j
  rectangularConstant : m.localization.indices → m.localization.indices → ℝ
  rectangularConstant_nonnegative : ∀ i j, 0 ≤ rectangularConstant i j
  weakConstant : m.localization.indices → m.localization.indices → ℝ
  weakConstant_nonnegative : ∀ i j, 0 ≤ weakConstant i j
  strongRows : ∀ a i j c,
    strongOutputNorm m pairMember a i j c ≤ strongConstant i j * inputStrongNorm m j c
  rectangularRows : ∀ a i j c,
    weakOutputNorm m pairMember a i j c ≤ rectangularConstant i j * inputHNorm m j c
  weakRows : ∀ a i j c,
    weakOutputNorm m pairMember a i j c ≤ weakConstant i j * inputWNorm m j c


variable (r : Data m)
namespace Data
@[expose] def strongBound : ℝ := ∑ i, ∑ j, r.strongConstant i j

@[expose] def rectangularBound : ℝ := ∑ i, ∑ j, r.rectangularConstant i j

@[expose] def weakBound : ℝ := ∑ i, ∑ j, r.weakConstant i j

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem strongBound_nonnegative : 0 ≤ r.strongBound :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => r.strongConstant_nonnegative i j

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem rectangularBound_nonnegative : 0 ≤ r.rectangularBound :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => r.rectangularConstant_nonnegative i j

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem weakBound_nonnegative : 0 ≤ r.weakBound :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => r.weakConstant_nonnegative i j

/- The global strong one-step bound is derived from actual local pair rows. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
private theorem strong_core_bound (a : Ω) (c : PhysicalManifoldModel.Core (E := E) V) :
    ‖targetCore m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      m.realize m.maps m.weight m.coreRegular a c‖ ≤ r.strongBound * ‖m.qa c‖ := by
  have h := CompletedRectangularCoreBound.core_bound m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    m.view m.regularCore m.regularCore_dense m.view_core m.evaluate m.evaluation
    m.localView m.localView_injective m.localCore m.localCore_dense m.localView_core
    m.localEvaluate m.localEvaluation m.coordinateConstant m.coordinateBound
    m.localBlocks m.blockConstant m.blockBound (m.core_zero_outside)
    m.view_injective (m.maps a) m.weight (m.coreRegular a) (r.pairMember a)
    m.localBlocks r.strongConstant r.strongConstant_nonnegative (r.strongRows a) c
  exact h

/- Exact smooth-input composition law for the constructed bounded generator. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
include r in
private theorem generator_core (a : Ω) (c : PhysicalManifoldModel.Core (E := E) V) :
    m.generator a (coreLift m.qa c) = m.realize
      (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
        m.maps m.weight m.coreRegular a c) :=
  operator_core m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
    m.realize m.maps m.weight m.coreRegular r.strongBound (r.strong_core_bound m) a c

/- One-step operator boundedness is derived from local rows, not supplied. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
private theorem generator_norm_le (a : Ω) : ‖m.generator a‖ ≤ r.strongBound :=
  operator_norm_le m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
    m.realize m.maps m.weight m.coreRegular r.strongBound (r.strong_core_bound m)
    (r.strongBound_nonnegative m) a

/- The rectangular bound is a deduction from primitive local one-step rows. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
private theorem rectangular_core_bound (a : Ω) (c : PhysicalManifoldModel.Core (E := E) V) :
    ‖FiniteRegularTransferBetweenSpaces.targetCore (SmoothSupportedManifoldCore.functions V)
      Reg m.view m.view_injective (weakRealize m) m.maps m.weight m.coreRegular a c‖ ≤
      r.rectangularBound * ‖m.qH c‖ := by
  change ‖(weakRealize m) (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view
    m.view_injective m.maps m.weight m.coreRegular a c)‖ ≤ _
  have h := CompletedRectangularCoreBound.core_bound m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    m.view m.regularCore m.regularCore_dense m.view_core m.evaluate m.evaluation
    m.localView m.localView_injective m.localCore m.localCore_dense m.localView_core
    m.localEvaluate m.localEvaluation m.coordinateConstant m.coordinateBound
    m.weakLocalBlocksW m.blockConstant (weak_block_bound m) (m.core_zero_outside)
    m.view_injective (m.maps a) m.weight (m.coreRegular a) (r.pairMember a)
    m.weakLocalBlocksH r.rectangularConstant r.rectangularConstant_nonnegative (r.rectangularRows a) c
  have hn : ‖CompletedChartPairTransfer.coreMap m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      m.weakLocalBlocksH c‖ = ‖m.qH c‖ :=
    congrArg (fun q => ‖q c‖) (weakHCoreMap m)
  calc
    ‖weakRealize m (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view
      m.view_injective m.maps m.weight m.coreRegular a c)‖ =
        ‖rawWeakRealize m (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view
          m.view_injective m.maps m.weight m.coreRegular a c)‖ := weakRealize_norm m _
    _ ≤ r.rectangularBound * ‖CompletedChartPairTransfer.coreMap m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
        m.weakLocalBlocksH c‖ := h
    _ = r.rectangularBound * ‖m.qH c‖ :=
      congrArg (fun z : ℝ => r.rectangularBound * z) hn

/- The weak-to-weak bound follows from the SAME constructed weak transfer. -/
omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
private theorem weak_core_bound (a : Ω) (c : PhysicalManifoldModel.Core (E := E) V) :
    ‖targetCore m.qW (SmoothSupportedManifoldCore.functions V)
      Reg m.view m.view_injective (weakRealize m) m.maps m.weight m.coreRegular a c‖ ≤
      r.weakBound * ‖m.qW c‖ := by
  change ‖(weakRealize m) (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view
    m.view_injective m.maps m.weight m.coreRegular a c)‖ ≤ _
  have h := CompletedRectangularCoreBound.core_bound m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
    m.view m.regularCore m.regularCore_dense m.view_core m.evaluate m.evaluation
    m.localView m.localView_injective m.localCore m.localCore_dense m.localView_core
    m.localEvaluate m.localEvaluation m.coordinateConstant m.coordinateBound
    m.weakLocalBlocksW m.blockConstant (weak_block_bound m) (m.core_zero_outside)
    m.view_injective (m.maps a) m.weight (m.coreRegular a) (r.pairMember a)
    m.weakLocalBlocksW r.weakConstant r.weakConstant_nonnegative (r.weakRows a) c
  have hn : ‖CompletedChartPairTransfer.coreMap m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      m.weakLocalBlocksW c‖ = ‖m.qW c‖ :=
    congrArg (fun q => ‖q c‖) (weakWCoreMap m)
  calc
    ‖weakRealize m (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view
      m.view_injective m.maps m.weight m.coreRegular a c)‖ =
        ‖rawWeakRealize m (regularAction (SmoothSupportedManifoldCore.functions V) Reg m.view
          m.view_injective m.maps m.weight m.coreRegular a c)‖ := weakRealize_norm m _
    _ ≤ r.weakBound * ‖CompletedChartPairTransfer.coreMap m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
        m.weakLocalBlocksW c‖ := h
    _ = r.weakBound * ‖m.qW c‖ :=
      congrArg (fun z : ℝ => r.weakBound * z) hn

/- Produced ordinary-core agreement and global one-step bounds. The public
record is generic; its nested physical proof terms remain private. -/
def produced : ProducedCoreRows.Data m.regularCore (coreLift m.qW) (weakRealize m)
    (fun a c => ‖targetCore m.qa (SmoothSupportedManifoldCore.functions V) Reg m.view
      m.view_injective m.realize m.maps m.weight m.coreRegular a c‖)
    (fun a c => ‖FiniteRegularTransferBetweenSpaces.targetCore
      (SmoothSupportedManifoldCore.functions V) Reg m.view m.view_injective
      (weakRealize m) m.maps m.weight m.coreRegular a c‖)
    (fun a c => ‖targetCore m.qW (SmoothSupportedManifoldCore.functions V) Reg m.view
      m.view_injective (weakRealize m) m.maps m.weight m.coreRegular a c‖)
    (fun c => ‖m.qa c‖) (fun c => ‖m.qH c‖) (fun c => ‖m.qW c‖)
    r.strongBound r.rectangularBound r.weakBound := {
  core := weakRealize_core m
  strong := r.strong_core_bound m
  rectangular := r.rectangular_core_bound m
  weak := r.weak_core_bound m
}

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldRowSources
