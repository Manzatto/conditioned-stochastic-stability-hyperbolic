module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.IntrinsicGeometricManifoldInputsWithWeakCore
public import LeanShared.Analysis.CompletedRealizationTransport
public import LeanShared.Analysis.DyadicInclusionNorm

/-! Precise classical intrinsic pressure and per-pair microscopic sources.
No finite strict block, global word estimate or noisy Lasota--Yorke bound is a
field: those are deductions of the actual chart and intrinsic-density pipeline.
The principal microscopic constant is independent of word length; only the
weak remainder may depend on a fixed block and bounded phase parameters.

Provenance: Baladi--Tsujii (2008), arXiv:math/0606434, Lemmas 4.14 and
4.17, Remark 4.15, and the finite-cylinder decomposition of Section 5.
The pressure limit is the deterministic minimum-cover coefficient limit
of Section 5, not an assumed strict random-word bound. The source's standing
saddle/cone scope must be checked by each manuscript application; this record
does not assert a pure-stable or pure-unstable endpoint extension. -/

public noncomputable section
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff SchwartzMap BigOperators Topology
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPressureSources
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



open LeanShared.CylinderPrincipalCoefficient LeanShared.PressureCoverRefinement
variable [MetricSpace Ω]
  {Fiber : M → Type*} [∀ x, NormedAddCommGroup (Fiber x)]
  [∀ x, InnerProductSpace ℝ (Fiber x)] [∀ x, FiniteDimensional ℝ (Fiber x)]
  {Params : Type*} {I : ℕ → Type*}

set_option maxHeartbeats 1600000 in
structure Data where
  T : Ω
  K : Set M
  hK : IsCompact K
  differential : ∀ a x, Fiber x ≃L[ℝ] Fiber (m.maps a x)
  envelope : M → ℝ
  stable : (x : M) → Submodule ℝ (Fiber x)
  unstable : (x : M) → Submodule ℝ (Fiber x)
  t : ℝ
  s : ℝ
  ht : 0 ≤ t
  hs : s ≤ 0
  chart : (N : ℕ) → I N → Set ((Fin N → Ω) × M)
  hchart : ∀ N i, IsOpen (chart N i)
  surviving : (N : ℕ) → Set ((Fin N → Ω) × M)
  closed : ∀ N, IsClosed (surviving N)
  cover : ∀ N, ∃ c : Finset (I N),
    fiber K (surviving N) (fun _ => T) ⊆
      ⋃ i ∈ c, (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i
  weight_continuous : ∀ N i, ContinuousOn
    (fun z => IntrinsicPrincipalDensity.weight m.maps envelope (List.ofFn z.1) z.2) (chart N i)
  jacobian_continuous : ∀ N i, ContinuousOn
    (fun z => IntrinsicPrincipalDensity.unstableJacobian m.maps Fiber differential
      (List.ofFn z.1) z.2 (unstable z.2)) (chart N i)
  stable_continuous : ∀ N i, ContinuousOn
    (fun z => IntrinsicPrincipalDensity.stableFactor m.maps Fiber differential
      (List.ofFn z.1) z.2 (stable (IntrinsicPrincipalDensity.orbit m.maps (List.ofFn z.1) z.2))) (chart N i)
  inverse_continuous : ∀ N i, ContinuousOn
    (fun z => IntrinsicPrincipalDensity.inverseFactor m.maps Fiber differential
      (List.ofFn z.1) z.2 (unstable z.2)) (chart N i)
  bounded : ∀ N i, BddAbove ({0} ∪
    (fun x => IntrinsicPrincipalDensity.density m.maps Fiber differential envelope stable unstable N t s ((fun _ => T), x)) ''
    (K ∩ (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i))
  parameters : (N : ℕ) → Params → (Fin N → Ω) → Prop
  parameterControl : ∀ N, ∃ p : Params, ∃ V : Set (Fin N → Ω),
    V ∈ 𝓝 (fun _ => T) ∧ ∀ word ∈ V, parameters N p word
  valid : (N : ℕ) → Set (Fin N → Ω)
  validNeighborhood : ∀ N, valid N ∈ 𝓝 (fun _ => T)
  Qpressure : ℝ
  Cmic : ℝ
  Cchart : ℝ
  ρ : ℝ
  hCmic : 0 ≤ Cmic
  hCchart : 0 ≤ Cchart
  positive : 0 < (Fintype.card m.localization.indices : ℝ) ^ 2 * (Cmic * Cchart)
  slack : Qpressure < ρ
  pressure : Tendsto (fun N =>
    (coverCoefficient K (fiber K (surviving N) (fun _ => T))
      (fun i => (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i)
      (fun x => IntrinsicPrincipalDensity.density m.maps Fiber differential envelope stable unstable N t s ((fun _ => T), x))) ^ ((N : ℝ)⁻¹)) atTop (𝓝 Qpressure)
  capture : ∀ N (c : Finset (I N)), (c → Set M) → Set M
  capture_open : ∀ N c v, IsOpen (capture N c v)
  capture_reference : ∀ N (c : Finset (I N)) (v : c → Set M),
    (∀ i, IsOpen (v i)) → (∀ i, IsCompact (closure (v i))) →
    (∀ i x, x ∈ closure (v i) → ((fun _ : Fin N => T), x) ∈ chart N i) →
    (fiber K (surviving N) (fun _ => T) ⊆ ⋃ i, v i) →
    fiber K (surviving N) (fun _ => T) ⊆ capture N c v
  pairMember : ∀ N (word : Fin N → Ω) i j
    (f : SchwartzJetSpace.supportedCore (ConstructedManifoldLocalization.support m.atlas m.localization j)),
    ChartPairTransfer.pair (m.atlas i) (m.atlas j) (m.localization.cutoff i)
      (ActualFiniteRegularWord.orbit m.maps (List.ofFn word))
      (ActualWordMicrolocalBound.realWeight m.maps m.weight (List.ofFn word)) f.val ∈ (m.localView i).range
  principal : ∀ N (c : Finset (I N)), (c → Set M) → Params →
    (Fin N → Ω) → m.localization.indices → m.localization.indices → ℝ
  remainder : ∀ N (c : Finset (I N)), (c → Set M) → Params → m.localization.indices → m.localization.indices → ℝ
  nonneg : ∀ N c v p i j, 0 ≤ remainder N c v p i j
  source : ∀ N (c : Finset (I N)) (v : c → Set M) p word,
    word ∈ valid N → parameters N p word →
    (∀ i, IsOpen (v i)) → (∀ i, IsCompact (closure (v i))) →
    (∀ i x, x ∈ closure (v i) → (word, x) ∈ chart N i) →
    (fiber K (surviving N) word ⊆ ⋃ i, v i) →
    (fiber K (surviving N) word ⊆ capture N c v) →
    (∀ i j, principal N c v p word i j ≤ Cchart *
      ∑ k, coefficient K (Set.univ ×ˢ closure (v k)) (IntrinsicPrincipalDensity.density m.maps Fiber differential envelope stable unstable N t s) word) ∧
    ∀ i j f,
      ‖localRealize m.atlas m.localization m.localCore m.localBlocks i
        (RegularChartPairTransfer.localPair m.atlas m.localization
          (ActualFiniteRegularWord.orbit m.maps (List.ofFn word))
          (ActualWordMicrolocalBound.realWeight m.maps m.weight (List.ofFn word))
          m.localView m.localView_injective (pairMember N word) i j
          (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) j f))‖ ≤
        (Cmic * principal N c v p word i j) *
          ‖m.localBlocks j (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) j f)‖ +
        remainder N c v p i j *
          ‖m.weakLocalBlocksW j (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) j f)‖

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPressureSources
