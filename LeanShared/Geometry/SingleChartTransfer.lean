module
public import LeanShared.Geometry.CompletedChartPairTransfer

/-! The weighted transfer of a function living in a single chart. If a core function is
the zero extension of a local function `f` in chart `j`, every chart coordinate of its
weighted composition is the literal chart-pair transfer of `f`; its completed
realization is therefore bounded by the pair bounds of `f` alone. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable
namespace LeanShared.SingleChartTransfer
open DyadicCompletion RegularChartPairTransfer

variable {E M AtlasIndex Core Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  (e : AtlasIndex → OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (view : Reg →ₗ[ℂ] (M → ℂ)) (inj : Function.Injective view)
  (F : M → M) (g : M → ℝ)
  (regular : ∀ c, FiniteRegularTransferRealization.weightedComposition F g (functions c) ∈ view.range)
  {LocalReg : D.indices → Type*} [∀ i, AddCommGroup (LocalReg i)] [∀ i, Module ℂ (LocalReg i)]
  (localView : ∀ i, LocalReg i →ₗ[ℂ] (E → ℂ)) (localInj : ∀ i, Function.Injective (localView i))
  (coordinateMember : ∀ i f, coordinate (e i) (D.cutoff i) (view f) ∈ (localView i).range)
  (pairMember : ∀ i j (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j)),
    ChartPairTransfer.pair (e i) (e j) (D.cutoff i) F g f.val ∈ (localView i).range)

/-- Every chart coordinate of the transfer of a single-chart function is a chart pair. -/
theorem coordinate_single (i j : D.indices)
    (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j))
    (c : Core) (hc : ∀ x, functions c x = if x ∈ (e j).source then f.val (e j x) else 0) :
    localCoordinate e D view localView localInj coordinateMember i
      (globalAction functions view inj F g regular c) =
      localPair e D F g localView localInj pairMember i j f := by
  apply localInj i
  have hv : view (globalAction functions view inj F g regular c) =
      FiniteRegularTransferRealization.weightedComposition F g (functions c) :=
    funext fun x => FiniteRegularTransferRealization.regularAction_apply
      functions Reg view inj (fun _ : Unit => F) g (fun _ => regular) () c x
  calc localView i (localCoordinate e D view localView localInj coordinateMember i
        (globalAction functions view inj F g regular c)) =
        coordinate (e i) (D.cutoff i) (view (globalAction functions view inj F g regular c)) :=
      lift_view (localView i) (localInj i) ((coordinate (e i) (D.cutoff i)).comp view)
        (coordinateMember i) _
    _ = ChartPairTransfer.pair (e i) (e j) (D.cutoff i) F g f.val := by
      rw [hv]
      funext y
      simp only [coordinate_apply, ChartLocalization.coordinate,
        ChartPairTransfer.pair_apply, ChartPairTransfer.weighted_apply, hc]
      split_ifs <;> ring
    _ = _ := (lift_view (localView i) (localInj i)
        ((ChartPairTransfer.pair (e i) (e j) (D.cutoff i) F g).comp (sourceFunction e D j))
        (pairMember i j) f).symm

section Completed
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
  {B : D.indices → Type*} [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℂ (B i)]
  [∀ i, CompleteSpace (B i)]
  (sourceBlock : ∀ i, SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D i) →ₗ[ℂ] B i)
  (Cblock : D.indices → ℝ)
  (blockBound : ∀ i f, ‖sourceBlock i f‖ ≤ Cblock i * ‖localCore i f‖)
  (inj : Function.Injective view) (F : M → M) (g : M → ℝ)
  (regular : ∀ c, FiniteRegularTransferRealization.weightedComposition F g (functions c) ∈ view.range)
  (pairMember : ∀ i j (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j)),
    ChartPairTransfer.pair (e i) (e j) (D.cutoff i) F g f.val ∈ (localView i).range)

include dense viewCore evaluation localViewCore localEvaluation coordinateBound localDense blockBound in
/-- The completed realization of the transfer of a single-chart function is bounded by
the pair bounds of its local function. -/
theorem realization_single_norm (j : D.indices)
    (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j))
    (c : Core) (hc : ∀ x, functions c x = if x ∈ (e j).source then f.val (e j x) else 0)
    (b : ℝ) (hb : 0 ≤ b)
    (pairBound : ∀ i, ‖localRealize e D localCore sourceBlock i
      (localPair e D F g localView localInj pairMember i j f)‖ ≤ b) :
    ‖realization e D he functions smooth regularCore dense localCore localDense Ccoord
      coordinateBound sourceBlock Cblock blockBound
      (globalAction functions view inj F g regular c)‖ ≤ b := by
  rw [realization_action_norm e D he functions smooth view regularCore dense viewCore evaluate
    evaluation localView localInj localCore localDense localViewCore localEvaluate localEvaluation
    Ccoord coordinateBound sourceBlock Cblock blockBound inj F g regular]
  refine (pi_norm_le_iff_of_nonneg hb).mpr fun i => ?_
  change ‖localRealize e D localCore sourceBlock i
    (localCoordinate e D view localView localInj (coordinate_member e D he functions smooth view
      regularCore dense viewCore evaluate evaluation localView localCore localViewCore
      localEvaluate localEvaluation Ccoord coordinateBound) i
      (globalAction functions view inj F g regular c))‖ ≤ b
  rw [coordinate_single e D functions view inj F g regular localView localInj
    (coordinate_member e D he functions smooth view regularCore dense viewCore evaluate evaluation
      localView localCore localViewCore localEvaluate localEvaluation Ccoord coordinateBound)
    pairMember i j f c hc]
  exact pairBound i

end Completed

end LeanShared.SingleChartTransfer
