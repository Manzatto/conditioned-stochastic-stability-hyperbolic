module

public import LeanShared.Geometry.CompletedMicrolocalEstimate
public import LeanShared.Analysis.ActualWordMicrolocalBound

/-!
# Actual manifold operator words from local chart microscopic estimates

The local chart-pair estimate is applied to the literal chronological word
and accumulated real weight. Its completed output is proved equal to the
word of the constructed generators, through ordinary finite-regular
invariance. In particular the global word inequality is a deduction rather
than an input to the subsequent pressure and random-word arguments.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff SchwartzMap BigOperators

namespace LeanShared.CompletedManifoldWordEstimate

open DyadicCompletion CompletedChartPairTransfer
open FiniteRegularTransferRealization FiniteBlockAnnealedEstimates

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


variable {Ω : Type*} (zero : ∀ c : Core, ∀ x ∉ S, functions c x = 0)
  (inj : Function.Injective view) (F : Ω → M → M) (g : M → ℝ)
  (invariant : ∀ a f, weightedComposition (F a) g (view f) ∈ view.range)
  (coreRegular : ∀ a c, weightedComposition (F a) g (functions c) ∈ view.range)
  (Creg : ℝ)
  (regularBound : ∀ a f,
    ‖InvariantFiniteRegularTransfer.action view inj F g invariant a f‖ ≤ Creg * ‖f‖)


variable (L : ℝ) (analyticBound : ∀ a c,
  ‖targetCore (coreMap e D he functions smooth sourceBlock) functions Reg view inj (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) F g coreRegular a c‖ ≤ L * ‖(coreMap e D he functions smooth sourceBlock) c‖)
  {W : D.indices → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℂ (W i)]
  (weakBlock : ∀ i, SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D i) →ₗ[ℂ] W i)

include dense viewCore evaluation localViewCore localEvaluation coordinateBound localDense blockBound zero invariant regularBound analyticBound in
/-- A local pair estimate for the literal finite word yields the completed
operator-word estimate. The squared atlas cardinality is independent of
word length, and the weak remainder may depend on the fixed block. -/
theorem word_core_bound (w : List Ω)
    (pairMember : ∀ i j (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j)),
      ChartPairTransfer.pair (e i) (e j) (D.cutoff i)
        (ActualFiniteRegularWord.orbit F w) (ActualWordMicrolocalBound.realWeight F g w) f.val ∈ (localView i).range)
    (C cost : ℝ) (hC : 0 ≤ C) (hcost : 0 ≤ cost)
    (remainder : D.indices → D.indices → ℝ) (hR : ∀ i j, 0 ≤ remainder i j)
    (pairBound : ∀ i j c,
      ‖localRealize e D localCore sourceBlock i
        (RegularChartPairTransfer.localPair e D
          (ActualFiniteRegularWord.orbit F w) (ActualWordMicrolocalBound.realWeight F g w)
          localView localInj pairMember i j
          (ConstructedManifoldLocalization.localize e D he functions smooth j c))‖ ≤
        (C * cost) * ‖sourceBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j c)‖ +
        remainder i j * ‖weakBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j c)‖)
    (c : Core) :
    ‖listWord (operator (coreMap e D he functions smooth sourceBlock) functions Reg view inj (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) F g coreRegular) w (coreLift (coreMap e D he functions smooth sourceBlock) c)‖ ≤
      ((Fintype.card D.indices : ℝ) ^ 2 * C * cost) * ‖coreLift (coreMap e D he functions smooth sourceBlock) c‖ +
      (∑ i, ∑ j, remainder i j) *
        ‖CompletedMicrolocalEstimate.weakCore e D he functions smooth weakBlock c‖ := by
  rw [← ActualWordMicrolocalBound.realized_whole_action (coreMap e D he functions smooth sourceBlock) functions regularCore dense view inj
    viewCore (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound)
    (realization_core e D he functions smooth regularCore dense localCore localDense
      Ccoord coordinateBound sourceBlock Cblock blockBound)
    F g invariant coreRegular Creg regularBound L analyticBound]
  exact CompletedMicrolocalEstimate.weighted_core_bound e D he functions smooth view regularCore dense viewCore
    evaluate evaluation localView localInj localCore localDense localViewCore localEvaluate localEvaluation
    Ccoord coordinateBound sourceBlock Cblock blockBound zero inj
    (ActualFiniteRegularWord.orbit F w) (ActualWordMicrolocalBound.realWeight F g w)
    (ActualWordMicrolocalBound.word_regular functions regularCore view inj viewCore F g invariant Creg regularBound w)
    pairMember weakBlock C cost hC hcost remainder hR pairBound c


include dense viewCore evaluation localViewCore localEvaluation coordinateBound localDense blockBound zero invariant regularBound analyticBound in
/-- Endpoint chart norm and Jacobian comparisons convert each local
principal coefficient to the same intrinsic cover cost. The resulting
atlas constant is fixed independently of the chosen word length. -/
theorem word_core_bound_of_coordinate_comparison (w : List Ω)
    (pairMember : ∀ i j (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j)),
      ChartPairTransfer.pair (e i) (e j) (D.cutoff i)
        (ActualFiniteRegularWord.orbit F w) (ActualWordMicrolocalBound.realWeight F g w) f.val ∈ (localView i).range)
    (Cmic Cchart cost : ℝ) (hCmic : 0 ≤ Cmic) (hCchart : 0 ≤ Cchart) (hcost : 0 ≤ cost)
    (principal : D.indices → D.indices → ℝ)
    (comparison : ∀ i j, principal i j ≤ Cchart * cost)
    (remainder : D.indices → D.indices → ℝ) (hR : ∀ i j, 0 ≤ remainder i j)
    (pairBound : ∀ i j c,
      ‖localRealize e D localCore sourceBlock i
        (RegularChartPairTransfer.localPair e D
          (ActualFiniteRegularWord.orbit F w) (ActualWordMicrolocalBound.realWeight F g w)
          localView localInj pairMember i j
          (ConstructedManifoldLocalization.localize e D he functions smooth j c))‖ ≤
        (Cmic * principal i j) * ‖sourceBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j c)‖ +
        remainder i j * ‖weakBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j c)‖)
    (c : Core) :
    ‖listWord (operator (coreMap e D he functions smooth sourceBlock) functions Reg view inj (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) F g coreRegular) w (coreLift (coreMap e D he functions smooth sourceBlock) c)‖ ≤
      ((Fintype.card D.indices : ℝ) ^ 2 * (Cmic * Cchart) * cost) * ‖coreLift (coreMap e D he functions smooth sourceBlock) c‖ +
      (∑ i, ∑ j, remainder i j) *
        ‖CompletedMicrolocalEstimate.weakCore e D he functions smooth weakBlock c‖ := by
  apply word_core_bound e D he functions smooth view regularCore dense viewCore evaluate evaluation
    localView localInj localCore localDense localViewCore localEvaluate localEvaluation
    Ccoord coordinateBound sourceBlock Cblock blockBound zero inj F g invariant coreRegular
    Creg regularBound L analyticBound weakBlock w pairMember
    (Cmic * Cchart) cost (mul_nonneg hCmic hCchart) hcost remainder hR
  intro i j c
  apply (pairBound i j c).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    Cmic * principal i j ≤ Cmic * (Cchart * cost) :=
      mul_le_mul_of_nonneg_left (comparison i j) hCmic
    _ = (Cmic * Cchart) * cost := (mul_assoc _ _ _).symm


/-- The actual canonical weak inclusion extends a microscopic core bound
to every completed input. Density is that of the constructed chart core;
no bound on nonsmooth completed inputs is a source assumption. -/
theorem completed_word_bound
    {Core' V' W' Ω' : Type*} [AddCommGroup Core'] [Module ℂ Core']
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [CompleteSpace V']
    [NormedAddCommGroup W'] [NormedSpace ℂ W']
    (q : Core' →ₗ[ℂ] V') (A : Ω' → closedCore q →L[ℂ] closedCore q)
    (weak : closedCore q →L[ℂ] W') (weakCore : Core' →ₗ[ℂ] W')
    (weak_core : ∀ c, weak (coreLift q c) = weakCore c)
    (w : List Ω') (α β : ℝ)
    (bound : ∀ c, ‖listWord A w (coreLift q c)‖ ≤
      α * ‖coreLift q c‖ + β * ‖weakCore c‖)
    (x : closedCore q) :
    ‖listWord A w x‖ ≤ α * ‖x‖ + β * ‖weak x‖ := by
  apply (coreLift_dense q).induction_on
    (p := fun x => ‖listWord A w x‖ ≤ α * ‖x‖ + β * ‖weak x‖) x
  · exact isClosed_le (listWord A w).continuous.norm
      ((continuous_const.mul continuous_norm).add
        (continuous_const.mul weak.continuous.norm))
  · intro c
    rw [weak_core]
    exact bound c

end LeanShared.CompletedManifoldWordEstimate
