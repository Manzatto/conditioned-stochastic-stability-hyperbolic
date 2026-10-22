module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPressureSources

/-! Ordinary cited deterministic pressure and microscopic data before any
strict contraction rate is chosen. Strict rate selection belongs to the
formalized deduction, rather than a classical source field. -/

public noncomputable section
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff SchwartzMap BigOperators Topology
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldClassicalPressureSources
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
  hCmic : 0 ≤ Cmic
  hCchart : 0 ≤ Cchart
  positive : 0 < (Fintype.card m.localization.indices : ℝ) ^ 2 * (Cmic * Cchart)
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

namespace Data
variable (p : Data m (Fiber := Fiber) (Params := Params) (I := I))

def withRate (ρ : ℝ) (slack : p.Qpressure < ρ) :
    PhysicalManifoldPressureSources.Data m (Fiber := Fiber) (Params := Params) (I := I) where
  T := p.T
  K := p.K
  hK := p.hK
  differential := p.differential
  envelope := p.envelope
  stable := p.stable
  unstable := p.unstable
  t := p.t
  s := p.s
  ht := p.ht
  hs := p.hs
  chart := p.chart
  hchart := p.hchart
  surviving := p.surviving
  closed := p.closed
  cover := p.cover
  weight_continuous := p.weight_continuous
  jacobian_continuous := p.jacobian_continuous
  stable_continuous := p.stable_continuous
  inverse_continuous := p.inverse_continuous
  bounded := p.bounded
  parameters := p.parameters
  parameterControl := p.parameterControl
  valid := p.valid
  validNeighborhood := p.validNeighborhood
  Qpressure := p.Qpressure
  Cmic := p.Cmic
  Cchart := p.Cchart
  hCmic := p.hCmic
  hCchart := p.hCchart
  positive := p.positive
  pressure := p.pressure
  capture := p.capture
  capture_open := p.capture_open
  capture_reference := p.capture_reference
  pairMember := p.pairMember
  principal := p.principal
  remainder := p.remainder
  nonneg := p.nonneg
  source := p.source
  ρ := ρ
  slack := slack

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withRate_rate_aux (ρ : ℝ) (slack : p.Qpressure < ρ) :
    (p.withRate m ρ slack).ρ = ρ := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withRate_rate (ρ : ℝ) (slack : p.Qpressure < ρ) :
    (p.withRate m ρ slack).ρ = ρ := withRate_rate_aux m p ρ slack

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withRate_t_aux (ρ : ℝ) (slack : p.Qpressure < ρ) :
    (p.withRate m ρ slack).t = p.t := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withRate_t (ρ : ℝ) (slack : p.Qpressure < ρ) :
    (p.withRate m ρ slack).t = p.t := withRate_t_aux m p ρ slack

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withRate_s_aux (ρ : ℝ) (slack : p.Qpressure < ρ) :
    (p.withRate m ρ slack).s = p.s := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withRate_s (ρ : ℝ) (slack : p.Qpressure < ρ) :
    (p.withRate m ρ slack).s = p.s := withRate_s_aux m p ρ slack

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldClassicalPressureSources
