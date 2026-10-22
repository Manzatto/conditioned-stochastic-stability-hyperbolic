module

public import LeanShared.Geometry.CompletedChartPairTransfer

/-!
# Actual completed rectangular core bound from local chart rows

The input and output exponents may differ. The output realization is the
constructed ordinary finite-regular chart realization. Cited one-step
local row estimates yield the whole genuine maximum-chart bound, including
the weak-to-weak and intermediate-to-weak cases used by the actual noise
model. No global weak core inequality is assumed.
-/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace LeanShared.CompletedRectangularCoreBound
open DyadicCompletion CompletedChartPairTransfer

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
  {Input : D.indices → Type*} [∀ i, NormedAddCommGroup (Input i)] [∀ i, NormedSpace ℂ (Input i)]
  (inputBlock : ∀ i, SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D i) →ₗ[ℂ] Input i)

include dense viewCore evaluation localViewCore localEvaluation coordinateBound localDense blockBound zero in
/-- The bound for the actual completed weighted composition follows from
local chart-pair estimates in the actual input chart norm. -/
theorem core_bound
    (constant : D.indices → D.indices → ℝ) (nonnegative : ∀ i j, 0 ≤ constant i j)
    (localBound : ∀ i j c,
      ‖localRealize e D localCore sourceBlock i
        (RegularChartPairTransfer.localPair e D F g localView localInj pairMember i j
          (ConstructedManifoldLocalization.localize e D he functions smooth j c))‖ ≤
        constant i j * ‖inputBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j c)‖)
    (c : Core) :
    ‖realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound
      (RegularChartPairTransfer.globalAction functions view inj F g regular c)‖ ≤
      (∑ i, ∑ j, constant i j) *
        ‖coreMap e D he functions smooth inputBlock c‖ := by
  rw [realization_action_norm e D he functions smooth view regularCore dense viewCore evaluate evaluation
    localView localInj localCore localDense localViewCore localEvaluate localEvaluation Ccoord coordinateBound
    sourceBlock Cblock blockBound inj F g regular]
  have h := RegularChartPairTransfer.output_norm_le e D he functions smooth zero view inj F g regular
    localView localInj
    (coordinate_member e D he functions smooth view regularCore dense viewCore evaluate evaluation
      localView localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound)
    pairMember (fun i => (localRealize e D localCore sourceBlock i).toLinearMap) c
    ‖coreMap e D he functions smooth inputBlock c‖ 0
    (norm_nonneg _) le_rfl constant (fun _ _ => 0) nonnegative (fun _ _ => le_rfl) (by
      intro i j
      change ‖localRealize e D localCore sourceBlock i
        (RegularChartPairTransfer.localPair e D F g localView localInj pairMember i j
          (ConstructedManifoldLocalization.localize e D he functions smooth j c))‖ ≤ _
      simpa only [zero_mul, add_zero] using (localBound i j c).trans
        (mul_le_mul_of_nonneg_left
          (norm_le_pi_norm (coreMap e D he functions smooth inputBlock c) j) (nonnegative i j)))
  simpa only [Finset.sum_const_zero, zero_mul, add_zero] using h

end LeanShared.CompletedRectangularCoreBound
