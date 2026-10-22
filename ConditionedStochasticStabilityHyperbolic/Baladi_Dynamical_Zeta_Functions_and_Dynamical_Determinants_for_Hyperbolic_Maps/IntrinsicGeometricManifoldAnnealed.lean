module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ManifoldIntrinsicAnnealed
public import LeanShared.Analysis.ContinuousIntrinsicPrincipalDensity

/-!
# Geometric manifold principal coefficient produces actual annealed bounds

The pressure density is the literal dependent-tangent-fiber expression:
actual word weight, derivative chain product, unstable volume Jacobian,
stable preimage restriction, and inverse transported-unstable derivative.
No arbitrary scalar density or global Euclidean conjugacy is supplied.
Only local continuity of the geometric components is needed; actual
Jacobian positivity and scalar density continuity are proved internally.

Classical per-pair principal constants are independent of the local map and
weight (Baladi--Tsujii 2008, Lemma 4.14 (4.25), Remark 4.15, Lemma 4.17).
The local source additionally uses a finite cylinder partition and the
endpoint/distortion comparison of Section 5. Its weak-remainder constant
may depend on the selected finite block and bounded fractional derivative
parameters. The uniform noisy global word and annealed bounds are derived.
-/

@[expose] public noncomputable section

open Set IsManifold Filter MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators Topology

namespace ConditionedStochasticStabilityHyperbolic.IntrinsicGeometricManifoldAnnealed

open LeanShared LeanShared.DyadicCompletion LeanShared.CompletedChartPairTransfer
open LeanShared.FiniteRegularTransferRealization LeanShared.FiniteBlockAnnealedEstimates
open LeanShared.CylinderPrincipalCoefficient LeanShared.PressureCoverRefinement
open LeanShared.AnnealedOperatorBounds

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
/-- Actual geometric scalar pressure and cited local chart estimates
produce the constructed manifold operator's uniform annealed power bound. -/
theorem exists_geometric_annealed_power_bound
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
    (hL : 0 ≤ L) (C₀ Mweak : ℝ) (hρ : 0 < ρ) (hρC₀ : ρ < C₀)
    (hM : 0 ≤ Mweak) (hMC₀ : Mweak ≤ C₀)
    (U₀ : Set Ω) (hU₀ : IsOpen U₀) (hTU₀ : T ∈ U₀)
    (weak_bound : ∀ a ∈ U₀, ∀ x,
      ‖weak ((operator (coreMap e D he functions smooth sourceBlock) functions Reg view inj (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) F g coreRegular) a x)‖ ≤ Mweak * ‖weak x‖) :
    ∃ U : Set Ω, IsOpen U ∧ T ∈ U ∧ U ⊆ U₀ ∧
      ∃ Cpower Dpower : ℝ, 0 ≤ Cpower ∧ 0 ≤ Dpower ∧
      ∀ {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
        (ζ : Z → Ω), (∀ z, ζ z ∈ U) →
        (∀ x, AEStronglyMeasurable (fun z => (operator (coreMap e D he functions smooth sourceBlock) functions Reg view inj (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) F g coreRegular) (ζ z) x) μ) →
        ∀ P : closedCore (coreMap e D he functions smooth sourceBlock) →L[ℂ] closedCore (coreMap e D he functions smooth sourceBlock),
          (∀ x, P x = ∫ z, (operator (coreMap e D he functions smooth sourceBlock) functions Reg view inj (realization e D he functions smooth regularCore dense localCore localDense Ccoord coordinateBound sourceBlock Cblock blockBound) F g coreRegular) (ζ z) x ∂μ) →
          ∀ n x, ‖(P ^ n) x‖ ≤ Cpower * ρ ^ n * ‖x‖ + Dpower * C₀ ^ n * ‖weak x‖ := by
  have continuous : ∀ N i, ContinuousOn
      (IntrinsicPrincipalDensity.density F Fiber differential envelope stable unstable N t s) (chart N i) :=
    fun N i => ContinuousIntrinsicPrincipalDensity.continuousOn_density F Fiber differential
      envelope stable unstable N t s ht hs (chart N i) (weight_continuous N i)
      (jacobian_continuous N i) (stable_continuous N i) (inverse_continuous N i)
  exact ManifoldIntrinsicAnnealed.exists_annealed_power_bound
    e D he functions smooth view regularCore dense viewCore evaluate evaluation
    localView localInj localCore localDense localViewCore localEvaluate localEvaluation
    Ccoord coordinateBound sourceBlock Cblock blockBound zero inj F g invariant coreRegular
    Creg regularBound L analyticBound weakBlock
    T K hK (fun N => IntrinsicPrincipalDensity.density F Fiber differential envelope stable unstable N t s)
    chart hchart surviving closed cover continuous bounded parameters parameterControl
    valid validNeighborhood Qpressure Cmic Cchart ρ hCmic hCchart positive slack pressure
    weak weak_core capture capture_open capture_reference pairMember principal remainder nonneg source
    hL C₀ Mweak hρ hρC₀ hM hMC₀ U₀ hU₀ hTU₀ weak_bound

end ConditionedStochasticStabilityHyperbolic.IntrinsicGeometricManifoldAnnealed
