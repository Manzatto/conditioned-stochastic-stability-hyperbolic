module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.IntrinsicPressureBlock
public import LeanShared.Geometry.CompletedManifoldWordEstimate
public import LeanShared.Analysis.CompactFiberCapture

/-!
# Actual manifold transfer blocks from intrinsic pressure and local rows

Only classical per-chart microscopic kernel estimates and endpoint
coordinate comparisons are inputs. The strong space, regular realization,
whole-word map, chart row decomposition and completed word bound are the
constructed ones. Intrinsic pressure selects a strict block, refined
surviving cover and one common generator neighborhood. There is no supplied
global word inequality, strict principal coefficient or semicontinuous
weak-remainder constant. The latter may depend on the selected finite
cover and outer neighborhoods: their partition derivatives are fixed
before the common nearby-word estimate is applied.
-/

@[expose] public noncomputable section

open Set IsManifold Filter
open scoped Manifold ContDiff SchwartzMap BigOperators Topology

namespace ConditionedStochasticStabilityHyperbolic.ManifoldIntrinsicBlock

open LeanShared LeanShared.DyadicCompletion LeanShared.CompletedChartPairTransfer
open LeanShared.FiniteRegularTransferRealization LeanShared.FiniteBlockAnnealedEstimates
open LeanShared.CylinderPrincipalCoefficient LeanShared.PressureCoverRefinement

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


variable [TopologicalSpace Ω] [T2Space M] [LocallyCompactSpace M]

include dense viewCore evaluation localViewCore localEvaluation coordinateBound localDense blockBound zero invariant regularBound analyticBound in
/-- The local microscopic theorem supplies pair estimates for each fixed
valid chart cylinder. Its principal endpoint comparison is an ordinary
coordinate norm/Jacobian bound, with a constant independent of word length.
The weak row remainder depends on the chosen finite block and its actual
bounded microscopic parameters. The theorem derives the global completed
strict block and its open generator neighborhood. -/
theorem exists_robust_completed_block
    {Params : Type*} {I : ℕ → Type*}
    (T : Ω) (K : Set M) (hK : IsCompact K)
    (d : (N : ℕ) → (Fin N → Ω) × M → ℝ)
    (chart : (N : ℕ) → I N → Set ((Fin N → Ω) × M))
    (hchart : ∀ N i, IsOpen (chart N i))
    (surviving : (N : ℕ) → Set ((Fin N → Ω) × M))
    (closed : ∀ N, IsClosed (surviving N))
    (cover : ∀ N, ∃ c : Finset (I N),
      fiber K (surviving N) (fun _ => T) ⊆
        ⋃ i ∈ c, (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i)
    (continuous : ∀ N i, ContinuousOn (d N) (chart N i))
    (bounded : ∀ N i, BddAbove ({0} ∪
      (fun x => d N ((fun _ => T), x)) ''
      (K ∩ (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i)))
    (parameters : (N : ℕ) → Params → (Fin N → Ω) → Prop)
    (parameterControl : ∀ N, ∃ p : Params, ∃ V : Set (Fin N → Ω),
      V ∈ 𝓝 (fun _ => T) ∧ ∀ word ∈ V, parameters N p word)
    (valid : (N : ℕ) → Set (Fin N → Ω))
    (validNeighborhood : ∀ N, valid N ∈ 𝓝 (fun _ => T))
    (Qpressure Cmic Cchart ρ : ℝ) (hCmic : 0 ≤ Cmic) (hCchart : 0 ≤ Cchart)
    (positive : 0 < (Fintype.card D.indices : ℝ) ^ 2 * (Cmic * Cchart))
    (slack : Qpressure < ρ)
    (pressure : Tendsto (fun N =>
      (coverCoefficient K (fiber K (surviving N) (fun _ => T))
        (fun i => (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i)
        (fun x => d N ((fun _ => T), x))) ^ ((N : ℝ)⁻¹)) atTop (𝓝 Qpressure))
    (weak : closedCore (coreMap e D he functions smooth sourceBlock) →L[ℂ] (∀ i, W i))
    (weak_core : ∀ c, weak (coreLift (coreMap e D he functions smooth sourceBlock) c) =
      CompletedMicrolocalEstimate.weakCore e D he functions smooth weakBlock c)
    (capture : ∀ N (c : Finset (I N)), (c → Set M) → Set M)
    (capture_open : ∀ N c v, IsOpen (capture N c v))
    (capture_reference : ∀ N (c : Finset (I N)) (v : c → Set M),
      (∀ i, IsOpen (v i)) → (∀ i, IsCompact (closure (v i))) →
      (∀ i x, x ∈ closure (v i) → ((fun _ : Fin N => T), x) ∈ chart N i) →
      (fiber K (surviving N) (fun _ => T) ⊆ ⋃ i, v i) →
      fiber K (surviving N) (fun _ => T) ⊆ capture N c v)
    (pairMember : ∀ N (word : Fin N → Ω) i j
      (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D j)),
      ChartPairTransfer.pair (e i) (e j) (D.cutoff i)
        (ActualFiniteRegularWord.orbit F (List.ofFn word))
        (ActualWordMicrolocalBound.realWeight F g (List.ofFn word)) f.val ∈ (localView i).range)
    (principal : ∀ N (c : Finset (I N)), (c → Set M) → Params →
      (Fin N → Ω) → D.indices → D.indices → ℝ)
    (remainder : ∀ N (c : Finset (I N)), (c → Set M) → Params → D.indices → D.indices → ℝ)
    (nonneg : ∀ N c v p i j, 0 ≤ remainder N c v p i j)
    (source : ∀ N (c : Finset (I N)) (v : c → Set M) p word,
      word ∈ valid N → parameters N p word →
      (∀ i, IsOpen (v i)) → (∀ i, IsCompact (closure (v i))) →
      (∀ i x, x ∈ closure (v i) → (word, x) ∈ chart N i) →
      (fiber K (surviving N) word ⊆ ⋃ i, v i) →
      (fiber K (surviving N) word ⊆ capture N c v) →
      (∀ i j, principal N c v p word i j ≤ Cchart *
        ∑ k, coefficient K (Set.univ ×ˢ closure (v k)) (d N) word) ∧
      ∀ i j f,
        ‖localRealize e D localCore sourceBlock i
          (RegularChartPairTransfer.localPair e D
            (ActualFiniteRegularWord.orbit F (List.ofFn word))
            (ActualWordMicrolocalBound.realWeight F g (List.ofFn word))
            localView localInj (pairMember N word) i j
            (ConstructedManifoldLocalization.localize e D he functions smooth j f))‖ ≤
          (Cmic * principal N c v p word i j) *
            ‖sourceBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j f)‖ +
          remainder N c v p i j *
            ‖weakBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j f)‖) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set Ω, IsOpen U ∧ T ∈ U ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ word : Fin N → Ω, (∀ i, word i ∈ U) →
        ∀ x : closedCore (coreMap e D he functions smooth sourceBlock),
          ‖listWord (operator (coreMap e D he functions smooth sourceBlock) functions Reg view inj (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) F g coreRegular) (List.ofFn word) x‖ ≤
            ρ ^ N * ‖x‖ + B * ‖weak x‖ := by
  classical
  obtain ⟨N, hN, c, v, p, O, hO, hvo, hvcompact, hword⟩ :=
    IntrinsicPressureBlock.exists_robust_strict_block T K hK d chart hchart surviving closed cover
      continuous bounded parameters parameterControl valid validNeighborhood
      Qpressure ((Fintype.card D.indices : ℝ) ^ 2 * (Cmic * Cchart)) ρ
      positive slack pressure
  have href := hword (fun _ => T) (mem_of_mem_nhds hO)
  obtain ⟨Ocap, hOcap, hTcap, hcapture⟩ := CompactFiberCapture.exists_open_capture K hK
    (surviving N) (closed N) (fun _ : Fin N => T) (capture N c v) (capture_open N c v)
    (capture_reference N c v hvo hvcompact href.2.2.1 href.2.2.2.1)
  obtain ⟨U, hU, hTU, hbox⟩ := RobustTwoNormBlock.exists_open_box_of_mem_nhds
    N T (O ∩ Ocap) (inter_mem hO (hOcap.mem_nhds hTcap))
  refine ⟨N, hN, U, hU, hTU, ∑ i, ∑ j, remainder N c v p i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => nonneg N c v p i j)), ?_⟩
  intro word hw x
  obtain ⟨hvalid, hparams, hchartword, hcover, hcost, hstrict⟩ := hword word (hbox word hw).1
  obtain ⟨comparison, microscopic⟩ := source N c v p word hvalid hparams hvo hvcompact hchartword hcover
    (hcapture word (hbox word hw).2)
  apply (CompletedManifoldWordEstimate.completed_word_bound (coreMap e D he functions smooth sourceBlock)
    (operator (coreMap e D he functions smooth sourceBlock) functions Reg view inj (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) F g coreRegular) weak
    (CompletedMicrolocalEstimate.weakCore e D he functions smooth weakBlock) weak_core
    (List.ofFn word)
    (((Fintype.card D.indices : ℝ) ^ 2 * (Cmic * Cchart)) *
      ∑ k, coefficient K (Set.univ ×ˢ closure (v k)) (d N) word)
    (∑ i, ∑ j, remainder N c v p i j) ?_ x).trans
  · exact add_le_add (mul_le_mul_of_nonneg_right hstrict.le (norm_nonneg x)) le_rfl
  · intro f
    exact CompletedManifoldWordEstimate.word_core_bound_of_coordinate_comparison
      e D he functions smooth view regularCore dense viewCore evaluate evaluation
      localView localInj localCore localDense localViewCore localEvaluate localEvaluation
      Ccoord coordinateBound sourceBlock Cblock blockBound zero inj F g invariant coreRegular
      Creg regularBound L analyticBound weakBlock (List.ofFn word) (pairMember N word)
      Cmic Cchart _ hCmic hCchart hcost (principal N c v p word) comparison
      (remainder N c v p) (nonneg N c v p) microscopic f

end ConditionedStochasticStabilityHyperbolic.ManifoldIntrinsicBlock
