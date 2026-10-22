module

public import LeanShared.Geometry.CompletedChartPairTransfer

/-!
# Actual completed manifold estimate from local microscopic pair bounds

The output is the constructed finite-regular realization in the actual
maximum chart completion. Its chart vector is identified with the proved
literal local pair decomposition. Per-pair bounds on the actual local
strong and weak source blocks imply the completed output estimate. The
principal constant contains only the fixed squared atlas cardinality;
weak remainders may depend on the chosen word block.

No completed global block inequality is assumed. This theorem is the
assembly step between classical local microlocal estimates and the new
uniform intrinsic-pressure/noise argument.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff SchwartzMap BigOperators

namespace LeanShared.CompletedMicrolocalEstimate

open DyadicCompletion
open CompletedChartPairTransfer

variable {E M AtlasIndex Core Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  (e : AtlasIndex → OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))
  (view : Reg →ₗ[ℂ] (M → ℂ))
  (regularCore : Core →ₗ[ℂ] Reg) (dense : DenseRange regularCore)
  (viewCore : ∀ c, view (regularCore c) = functions c)
  (evaluate : M → Reg →L[ℂ] ℂ) (evaluation : ∀ x f, evaluate x f = view f x)
  {LocalReg : D.indices → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  (localView : ∀ i, LocalReg i →ₗ[ℂ] (E → ℂ)) (localInj : ∀ i, Function.Injective (localView i))
  (localCore : ∀ i, SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D i) →ₗ[ℂ] LocalReg i)
  (localDense : ∀ i, DenseRange (localCore i))
  (localViewCore : ∀ i f, localView i (localCore i f) = f.val)
  (localEvaluate : ∀ i, E → LocalReg i →L[ℂ] ℂ)
  (localEvaluation : ∀ i x f, localEvaluate i x f = localView i f x)
  (Ccoord : D.indices → ℝ)
  (coordinateBound : ∀ i c,
    ‖localCore i (ConstructedManifoldLocalization.localize e D he functions smooth i c)‖ ≤ Ccoord i * ‖regularCore c‖)

variable {B : D.indices → Type*} [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℂ (B i)]
  [∀ i, CompleteSpace (B i)]
  (sourceBlock : ∀ i, SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D i) →ₗ[ℂ] B i)
  (Cblock : D.indices → ℝ)
  (blockBound : ∀ i f, ‖sourceBlock i f‖ ≤ Cblock i * ‖localCore i f‖)


variable (zero : ∀ c : Core, ∀ x ∉ S, functions c x = 0)
  (inj : Function.Injective view) (F : M → M) (g : M → ℝ)
  (regular : ∀ c, FiniteRegularTransferRealization.weightedComposition F g (functions c) ∈ view.range)
  (pairMember : ∀ i j (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j)),
    ChartPairTransfer.pair (e i) (e j) (D.cutoff i) F g f.val ∈ (localView i).range)
  {W : D.indices → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℂ (W i)]
  (weakBlock : ∀ i, SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D i) →ₗ[ℂ] W i)

/-- The weak input norm uses the same genuine localization as the strong. -/
def weakCore : Core →ₗ[ℂ] (∀ i, W i) := LinearMap.pi fun i =>
  (weakBlock i).comp (ConstructedManifoldLocalization.localize e D he functions smooth i)

include dense viewCore evaluation localViewCore localEvaluation coordinateBound localDense blockBound zero in
/-- A cited local pair bound gives the actual completed weighted-core
estimate. All coordinates, membership and global realization were already
constructed; no global word estimate or norm identity is a hypothesis. -/
theorem weighted_core_bound (C cost : ℝ) (hC : 0 ≤ C) (hcost : 0 ≤ cost)
    (remainder : D.indices → D.indices → ℝ) (hR : ∀ i j, 0 ≤ remainder i j)
    (pairBound : ∀ i j c,
      ‖localRealize e D localCore sourceBlock i
        (RegularChartPairTransfer.localPair e D F g localView localInj pairMember i j
          (ConstructedManifoldLocalization.localize e D he functions smooth j c))‖ ≤
        (C * cost) * ‖sourceBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j c)‖ +
        remainder i j * ‖weakBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j c)‖)
    (c : Core) :
    ‖realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound
      (RegularChartPairTransfer.globalAction functions view inj F g regular c)‖ ≤
      ((Fintype.card D.indices : ℝ) ^ 2 * C * cost) *
        ‖coreLift (coreMap e D he functions smooth sourceBlock) c‖ +
      (∑ i, ∑ j, remainder i j) * ‖weakCore e D he functions smooth weakBlock c‖ := by
  rw [realization_action_norm e D he functions smooth view regularCore dense viewCore evaluate evaluation
    localView localInj localCore localDense localViewCore localEvaluate localEvaluation Ccoord coordinateBound
    sourceBlock Cblock blockBound inj F g regular]
  apply RegularChartPairTransfer.output_norm_le_common_principal e D he functions smooth zero view inj F g regular
    localView localInj
    (coordinate_member e D he functions smooth view regularCore dense viewCore evaluate evaluation
      localView localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound)
    pairMember (fun i => (localRealize e D localCore sourceBlock i).toLinearMap) c
    ‖coreLift (coreMap e D he functions smooth sourceBlock) c‖
    ‖weakCore e D he functions smooth weakBlock c‖ C cost
    (norm_nonneg _) (norm_nonneg _) hC hcost remainder hR
  intro i j
  exact (pairBound i j c).trans (add_le_add
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm
      (coreMap e D he functions smooth sourceBlock c) j) (mul_nonneg hC hcost))
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm
      (weakCore e D he functions smooth weakBlock c) j) (hR i j)))

end LeanShared.CompletedMicrolocalEstimate
