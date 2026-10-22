module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldClassicalPressureSources
public import LeanShared.Analysis.ChartWordControlFamily
public import LeanShared.Geometry.ChartWordSurvivors

/-! Ordinary microscopic/pressure inputs BEFORE common nearby-word controls.
The parameter arrays are literal actual endpoint-chart word Controls. Their
parameterControl and validNeighborhood conclusions are constructed from
local fractional composition bounds, deterministic cone geometry, actual
derivative continuity and compact moving survivor fibers. -/

public noncomputable section
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff SchwartzMap BigOperators Topology
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPreControlSources
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
  {I : ℕ → Type*}


set_option maxHeartbeats 1600000 in
structure Data where
  r : ℝ
  regularity_gt_one : 1 < r
  T : Ω
  maps : Ω → M ≃ₜ M
  maps_eq : ∀ a, m.maps a = maps a
  controls : ∀ N, (Fin (N + 1) → m.localization.indices) →
    ChartWordControlSystem.Data (E := E) maps T N
  control_out : ∀ N labels, (controls N labels).out = m.atlas (labels 0)
  control_inp : ∀ N labels, (controls N labels).inp = m.atlas (labels (Fin.last N))
  control_cutoff : ∀ N labels, (controls N labels).θ = m.localization.cutoff (labels 0)
  control_weight : ∀ N labels, (controls N labels).g = m.weight
  control_source : ∀ N labels, (controls N labels).K =
    ConstructedManifoldLocalization.support m.atlas m.localization (labels 0)
  control_target : ∀ N labels, (controls N labels).L =
    ConstructedManifoldLocalization.support m.atlas m.localization (labels (Fin.last N))
  control_order : ∀ N labels, ((controls N labels).m : ℝ) + (controls N labels).δ = r
  K : Set M
  hK : IsCompact K
  core_in_live : V ⊆ K
  control_survivors : ∀ N labels, (controls N labels).R =
    ChartWordSurvivors.relation (m.atlas (labels 0)) m.maps m.localization.cutoff K N labels
      (ConstructedManifoldLocalization.support m.atlas m.localization (labels 0))
  control_backward : ∀ N labels, (controls N labels).Rback =
    (univ ×ˢ ConstructedManifoldLocalization.support m.atlas m.localization (labels (Fin.last N))) ∩
      {z | (IntrinsicWordDifferential.wordHomeomorph maps (List.ofFn z.1)).symm
          ((m.atlas (labels (Fin.last N))).symm z.2) ∈ (m.atlas (labels 0)).source ∧
        (z.1, m.atlas (labels 0)
          ((IntrinsicWordDifferential.wordHomeomorph maps (List.ofFn z.1)).symm
            ((m.atlas (labels (Fin.last N))).symm z.2))) ∈
            ChartWordSurvivors.relation (m.atlas (labels 0)) m.maps m.localization.cutoff K N labels
              (ConstructedManifoldLocalization.support m.atlas m.localization (labels 0))}
  differential : ∀ a x, Fiber x ≃L[ℝ] Fiber (m.maps a x)
  envelope : M → ℝ
  stable : (x : M) → Submodule ℝ (Fiber x)
  unstable : (x : M) → Submodule ℝ (Fiber x)
  t : ℝ
  s : ℝ
  ht : 0 ≤ t
  hs : s ≤ 0
  admissible : t - s < r - 1
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
  principal : ∀ N (c : Finset (I N)), (c → Set M) → (ChartWordControlFamily.Parameters (fun N => Fin (N + 1) → m.localization.indices)) →
    (Fin N → Ω) → m.localization.indices → m.localization.indices → ℝ
  remainder : ∀ N (c : Finset (I N)), (c → Set M) → (ChartWordControlFamily.Parameters (fun N => Fin (N + 1) → m.localization.indices)) → m.localization.indices → m.localization.indices → ℝ
  nonneg : ∀ N c v p i j, 0 ≤ remainder N c v p i j
  source : ∀ N (c : Finset (I N)) (v : c → Set M) p word,
    word ∈ ChartWordControlFamily.valid controls N → ChartWordControlFamily.predicate controls N p word →
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
variable (p : Data m (Fiber := Fiber) (I := I))

set_option maxHeartbeats 1600000 in
def withControl : PhysicalManifoldClassicalPressureSources.Data m
    (Fiber := Fiber) (Params := (ChartWordControlFamily.Parameters (fun N => Fin (N + 1) → m.localization.indices))) (I := I) where
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
  parameters := ChartWordControlFamily.predicate p.controls
  parameterControl := ChartWordControlFamily.parameter_control p.controls
  valid := ChartWordControlFamily.valid p.controls
  validNeighborhood := ChartWordControlFamily.valid_neighborhood p.controls
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

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_T_aux : (p.withControl m).T = p.T := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_T : (p.withControl m).T = p.T :=
  withControl_T_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_K_aux : (p.withControl m).K = p.K := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_K : (p.withControl m).K = p.K :=
  withControl_K_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_differential_aux : (p.withControl m).differential = p.differential := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_differential : (p.withControl m).differential = p.differential :=
  withControl_differential_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_envelope_aux : (p.withControl m).envelope = p.envelope := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_envelope : (p.withControl m).envelope = p.envelope :=
  withControl_envelope_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_stable_aux : (p.withControl m).stable = p.stable := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_stable : (p.withControl m).stable = p.stable :=
  withControl_stable_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_unstable_aux : (p.withControl m).unstable = p.unstable := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_unstable : (p.withControl m).unstable = p.unstable :=
  withControl_unstable_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_t_aux : (p.withControl m).t = p.t := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_t : (p.withControl m).t = p.t :=
  withControl_t_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_s_aux : (p.withControl m).s = p.s := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_s : (p.withControl m).s = p.s :=
  withControl_s_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_chart_aux : (p.withControl m).chart = p.chart := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_chart : (p.withControl m).chart = p.chart :=
  withControl_chart_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_surviving_aux : (p.withControl m).surviving = p.surviving := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_surviving : (p.withControl m).surviving = p.surviving :=
  withControl_surviving_aux m p

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
private theorem withControl_Qpressure_aux : (p.withControl m).Qpressure = p.Qpressure := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [∀ k, CompleteSpace (LocalReg k)] in
theorem withControl_Qpressure : (p.withControl m).Qpressure = p.Qpressure :=
  withControl_Qpressure_aux m p


end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPreControlSources
