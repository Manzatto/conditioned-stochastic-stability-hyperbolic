module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.IntrinsicGeometricManifoldAnnealed
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedFiniteRegularAnnealedInputs

/-!
# Intrinsic manifold microscopic sources construct actual KL inputs

The robust block and simultaneous completed approximants are deductions.
Classical inputs describe ordinary finite-Hölder embeddings, microscopic
chart rows, tangent coefficient continuity and scalar pressure. The output
generator is the same constructed manifold weighted transfer throughout.
Canonical physical compact inclusions supply i, j and their exact core laws;
they are the maps already constructed by ManifoldCompactEmbedding.
-/

@[expose] public noncomputable section
open Set IsManifold Filter MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.IntrinsicGeometricManifoldInputsWithWeakCore
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
  {W : D.indices → Type*} [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℂ (W i)] [∀ i, CompleteSpace (W i)]
  (weakBlock : ∀ i, SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support e D i) →ₗ[ℂ] W i)


variable [MetricSpace Ω] [T2Space M] [LocallyCompactSpace M]



include dense viewCore evaluation localViewCore localEvaluation coordinateBound localDense blockBound zero invariant regularBound analyticBound in
/-- Neither robust block nor actual KL hypotheses are supplied inputs. -/
theorem exists_actual_annealed_inputs
    {Params : Type*} {I : ℕ → Type*}
    (T : Ω) (K : Set M) (hK : IsCompact K)
    (Fiber : M → Type*) [∀ x, NormedAddCommGroup (Fiber x)]
    [∀ x, InnerProductSpace ℝ (Fiber x)] [∀ x, FiniteDimensional ℝ (Fiber x)]
    (differential : ∀ a x, Fiber x ≃L[ℝ] Fiber (F a x))
    (envelope : M → ℝ) (stable unstable : (x : M) → Submodule ℝ (Fiber x))
    (t s : ℝ) (ht : 0 ≤ t) (hs : s ≤ 0)
    (chart : (N : ℕ) → I N → Set ((Fin N → Ω) × M))
    (hchart : ∀ N i, IsOpen (chart N i))
    (surviving : (N : ℕ) → Set ((Fin N → Ω) × M))
    (closed : ∀ N, IsClosed (surviving N))
    (cover : ∀ N, ∃ c : Finset (I N),
      fiber K (surviving N) (fun _ => T) ⊆
        ⋃ i ∈ c, (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i)
    (weight_continuous : ∀ N i, ContinuousOn
      (fun z => IntrinsicPrincipalDensity.weight F envelope (List.ofFn z.1) z.2) (chart N i))
    (jacobian_continuous : ∀ N i, ContinuousOn
      (fun z => IntrinsicPrincipalDensity.unstableJacobian F Fiber differential
        (List.ofFn z.1) z.2 (unstable z.2)) (chart N i))
    (stable_continuous : ∀ N i, ContinuousOn
      (fun z => IntrinsicPrincipalDensity.stableFactor F Fiber differential
        (List.ofFn z.1) z.2 (stable (IntrinsicPrincipalDensity.orbit F (List.ofFn z.1) z.2))) (chart N i))
    (inverse_continuous : ∀ N i, ContinuousOn
      (fun z => IntrinsicPrincipalDensity.inverseFactor F Fiber differential
        (List.ofFn z.1) z.2 (unstable z.2)) (chart N i))
    (bounded : ∀ N i, BddAbove ({0} ∪
      (fun x => IntrinsicPrincipalDensity.density F Fiber differential envelope stable unstable N t s ((fun _ => T), x)) ''
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
        (fun x => IntrinsicPrincipalDensity.density F Fiber differential envelope stable unstable N t s ((fun _ => T), x))) ^ ((N : ℝ)⁻¹)) atTop (𝓝 Qpressure))
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
        ∑ k, coefficient K (Set.univ ×ˢ closure (v k)) (IntrinsicPrincipalDensity.density F Fiber differential envelope stable unstable N t s) word) ∧
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
            ‖weakBlock j (ConstructedManifoldLocalization.localize e D he functions smooth j f)‖)

    (qW : Core →ₗ[ℂ] (∀ k, W k))
    (weak_core_eq : ∀ c, qW c = CompletedMicrolocalEstimate.weakCore e D he functions smooth weakBlock c)
    {Hbase Low Z : Type*} [NormedAddCommGroup Hbase] [NormedSpace ℂ Hbase]
    [NormedAddCommGroup Low] [NormedSpace ℂ Low]
    [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] [SecondCountableTopology Z]
    (qH : Core →ₗ[ℂ] Hbase)
    (lowView : Low →ₗ[ℂ] (M → ℂ)) (lowInj : Function.Injective lowView)
    (downgrade : Reg →L[ℂ] Low) (view_downgrade : ∀ f, lowView (downgrade f) = view f)
    (lowRegular : ∀ a c, weightedComposition (F a) g (functions c) ∈ lowView.range)
    (realizeWeak : Low →L[ℂ] closedCore qW)
    (weak_realize_core : ∀ c, realizeWeak (downgrade (regularCore c)) = coreLift qW c)
    (i : closedCore (coreMap e D he functions smooth sourceBlock) →L[ℂ] closedCore qH) (i_compact : IsCompactOperator i)
    (j : closedCore (coreMap e D he functions smooth sourceBlock) →L[ℂ] closedCore qW)
    (i_core : ∀ c, i (coreLift (coreMap e D he functions smooth sourceBlock) c) = coreLift qH c)
    (j_core : ∀ c, j (coreLift (coreMap e D he functions smooth sourceBlock) c) = coreLift qW c)
    (LW LWstep : ℝ) (hL : 0 ≤ L) (hLW : 0 ≤ LW) (hLWstep : 0 ≤ LWstep)
    (rect_core : ∀ a c,
      ‖FiniteRegularTransferBetweenSpaces.targetCore functions Low lowView lowInj realizeWeak F g lowRegular a c‖ ≤ LW * ‖qH c‖)
    (weak_step_core : ∀ a c,
      ‖targetCore qW functions Low lowView lowInj realizeWeak F g lowRegular a c‖ ≤ LWstep * ‖qW c‖)
    (low_core_limit : ∀ c, Tendsto (fun a => regularAction functions Low lowView lowInj F g lowRegular a c)
      (𝓝 T) (𝓝 (regularAction functions Low lowView lowInj F g lowRegular T c)))
    (noise : ℝ≥0 → Z → Ω) (noiseConstant : ℝ)
    (close : ∀ ε z, dist (noise ε z) T ≤ noiseConstant * (ε : ℝ))
    (law : ℝ≥0 → Measure Z) [∀ ε, IsProbabilityMeasure (law ε)]
    (noise_core : ∀ ε c, Continuous (fun z => regularAction functions Reg view inj F g coreRegular (noise ε z) c))
    (weakRate scale : ℝ) (hρ : 0 < ρ) (hrate : ρ < weakRate)
    (hweakRate : LWstep ≤ weakRate) (hscale : 1 ≤ scale) (hρscale : ρ < scale) :
    ∃ inputs : KellerLiverani1999.ActualAnnealedInputs law
        (fun ε => (inferInstance : IsProbabilityMeasure (law ε))) j scale,
      ∀ ε z, inputs.generator ε z =
        operator (coreMap e D he functions smooth sourceBlock) functions Reg view inj (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) F g coreRegular (noise ε z) := by
  have continuous : ∀ N k, ContinuousOn
      (IntrinsicPrincipalDensity.density F Fiber differential envelope stable unstable N t s) (chart N k) :=
    fun N k => ContinuousIntrinsicPrincipalDensity.continuousOn_density F Fiber differential
      envelope stable unstable N t s ht hs (chart N k) (weight_continuous N k)
      (jacobian_continuous N k) (stable_continuous N k) (inverse_continuous N k)
  let weakAmbient := (closedCore qW).subtypeL.comp j
  have weakAmbient_core : ∀ c, weakAmbient (coreLift (coreMap e D he functions smooth sourceBlock) c) =
      CompletedMicrolocalEstimate.weakCore e D he functions smooth weakBlock c := by
    intro c
    change (j (coreLift (coreMap e D he functions smooth sourceBlock) c) : ∀ k, W k) =
      CompletedMicrolocalEstimate.weakCore e D he functions smooth weakBlock c
    rw [j_core]
    exact weak_core_eq c
  obtain ⟨N, hN, U, hU, hTU, B, hB, hblock⟩ :=
    ManifoldIntrinsicBlock.exists_robust_completed_block
      e D he functions smooth view regularCore dense viewCore evaluate evaluation
      localView localInj localCore localDense localViewCore localEvaluate localEvaluation
      Ccoord coordinateBound sourceBlock Cblock blockBound zero inj F g invariant coreRegular
      Creg regularBound L analyticBound weakBlock T K hK
      (fun N => IntrinsicPrincipalDensity.density F Fiber differential envelope stable unstable N t s)
      chart hchart surviving closed cover continuous bounded parameters parameterControl
      valid validNeighborhood Qpressure Cmic Cchart ρ hCmic hCchart positive slack pressure
      weakAmbient weakAmbient_core capture capture_open capture_reference pairMember principal remainder nonneg source
  exact ConstructedFiniteRegularAnnealedInputs.exists_inputs_of_regular_density
    (coreMap e D he functions smooth sourceBlock) qH qW functions view inj lowView lowInj downgrade view_downgrade F g coreRegular lowRegular
    (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) realizeWeak i i_compact j i_core j_core regularCore dense
    (realization_core e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound)
    weak_realize_core L LW hL hLW analyticBound rect_core T low_core_limit
    noise noiseConstant close law noise_core LWstep hLWstep weak_step_core
    N hN ρ weakRate scale hρ hrate hweakRate hscale hρscale U (hU.mem_nhds hTU) B hB hblock

end ConditionedStochasticStabilityHyperbolic.IntrinsicGeometricManifoldInputsWithWeakCore
