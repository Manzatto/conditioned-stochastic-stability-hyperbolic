module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldClassicalPressureSources
public import LeanShared.Analysis.ChartWordControlFamily
public import LeanShared.Geometry.ChartWordSurvivors
public import LeanShared.Geometry.ClosedAtlasWordCylinders
public import LeanShared.Analysis.IntrinsicNearbyPrincipalCoefficient
public import LeanShared.Analysis.NarrowChartWordControls
public import LeanShared.Analysis.IntrinsicDistortionContinuity
public import LeanShared.Geometry.FiniteSmoothCapturePartition
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldPreControlSources

/-! Raw separate-supremum microscopic inputs and DETERMINISTIC full-cylinder distortion.
The parameter arrays are literal actual endpoint-chart word Controls.
The weak remainder retains the selected cover/outer-neighborhood dependence.
For that selected cover, `FiniteSmoothCapturePartition.data` constructs one
smooth partition before the random word is chosen. The raw local kernel
estimate below is used only on words whose survivor fiber lies in its open
sum-one region. CompactFiberCapture proves that this holds on one common
nearby-word neighborhood; no random partition robustness is assumed.
The ordinary local source is Baladi--Tsujii, Dynamical determinants and
spectrum for hyperbolic diffeomorphisms (2008), Lemma 4.14/Remark 4.15 and
Section 5, with the fixed partition derivative norms in the weak constant.
Only the principal constant is independent of word length.
The parameterControl and validNeighborhood conclusions are constructed from
local fractional composition bounds, deterministic cone geometry, actual
derivative continuity and compact moving survivor fibers. -/

public noncomputable section
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff SchwartzMap BigOperators Topology
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPreDistortionSources
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
  Ccoordinate : ℝ
  hCmic : 0 ≤ Cmic
  hCcoordinate : 0 ≤ Ccoordinate
  positive : 0 < (Fintype.card m.localization.indices : ℝ) ^ 2 * (Cmic * Ccoordinate)
  pressure : Tendsto (fun N =>
    (coverCoefficient K (fiber K (surviving N) (fun _ => T))
      (fun i => (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i)
      (fun x => IntrinsicPrincipalDensity.density m.maps Fiber differential envelope stable unstable N t s ((fun _ => T), x))) ^ ((N : ℝ)⁻¹)) atTop (𝓝 Qpressure)
  /-- Ordinary deterministic full-cylinder distortion, with constants independent of N.
  BT §5 uses the summable orbital error and actual unstable log-Jacobian
  distortion; this does not follow merely from values on the isolated core. -/
  epsilon : ℝ
  epsilon_positive : 0 < epsilon
  envelope_identity : envelope = fun x => m.weight x + epsilon
  weight_nonnegative : ∀ x, 0 ≤ m.weight x
  actual_weight_continuous : Continuous m.weight
  cylinderLabel : ∀ N, I N → (Fin (N + 1) → m.localization.indices)
  chart_in_closed : ∀ N i, chart N i ⊆
    ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N (cylinderLabel N i)
  maps_continuous : Continuous (fun z : Ω × M => m.maps z.1 z.2)
  distortionH : ℝ
  distortionB : ℝ
  distortionJ : ℝ
  distortionH_nonnegative : 0 ≤ distortionH
  ratioDomain : ∀ N, (Fin (N + 1) → m.localization.indices) → Set (Fin N → Ω)
  ratioDomain_open : ∀ N labels, IsOpen (ratioDomain N labels)
  ratioDomain_reference : ∀ N labels, (fun _ => T) ∈ ratioDomain N labels
  jacobian_closed_continuous : ∀ N labels, ContinuousOn
    (fun z : (Fin N → Ω) × M => IntrinsicPrincipalDensity.unstableJacobian
      m.maps Fiber differential (List.ofFn z.1) z.2 (unstable z.2))
    ((ratioDomain N labels ×ˢ univ) ∩
      ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels)
  error : ∀ N, (Fin (N + 1) → m.localization.indices) → M → M → Fin N → ℝ
  deterministic_increment : ∀ N labels x, x ∈ fiber K
      (ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels) (fun _ => T) →
    ∀ z, z ∈ fiber K (ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels) (fun _ => T) →
    ∀ j : Fin N, |m.weight (prefixOrbit m.maps (fun _ : Fin N => T) j.val x) -
      m.weight (prefixOrbit m.maps (fun _ : Fin N => T) j.val z)| ≤ distortionH * error N labels x z j
  deterministic_sum : ∀ N labels x, x ∈ fiber K
      (ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels) (fun _ => T) →
    ∀ z, z ∈ fiber K (ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels) (fun _ => T) →
    (∑ j, error N labels x z j) ≤ distortionB
  deterministic_jacobian : ∀ N labels y, y ∈ fiber K
      (ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels) (fun _ => T) →
    ∀ z, z ∈ fiber K (ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels) (fun _ => T) →
    |Real.log (IntrinsicPrincipalDensity.unstableJacobian m.maps Fiber differential (List.ofFn (fun _ : Fin N => T)) z (unstable z)) -
      Real.log (IntrinsicPrincipalDensity.unstableJacobian m.maps Fiber differential (List.ofFn (fun _ : Fin N => T)) y (unstable y))| ≤ distortionJ
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
    (fiber K (surviving N) word ⊆ (FiniteSmoothCapturePartition.data (E := E) (fiber K (surviving N) (fun _ : Fin N => T)) (fiber_isCompact hK (closed N) _) v).capture) →
    (∀ i j, principal N c v p word i j ≤ Ccoordinate *
      ∑ k, coefficient K (Set.univ ×ˢ closure (v k)) (IntrinsicPrincipalSuprema.originalWeight m.maps m.weight N) word *
        coefficient K (Set.univ ×ˢ closure (v k)) (IntrinsicPrincipalSuprema.inverseJacobian m.maps Fiber differential unstable N) word *
        coefficient K (Set.univ ×ˢ closure (v k)) (IntrinsicPrincipalSuprema.hyperbolicity m.maps Fiber differential stable unstable N t s) word) ∧
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

omit [∀ k, CompleteSpace (LocalReg k)] in
private theorem nearby (N : ℕ) (labels : Fin (N + 1) → m.localization.indices) : type_of% (
  IntrinsicNearbyPrincipalCoefficient.exists_uniform_separate_bound m.maps Fiber p.differential
    p.stable p.unstable m.weight p.weight_nonnegative N p.T p.K p.hK
    (ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels)
    (ClosedAtlasWordCylinders.cylinder_closed _ _ p.maps_continuous N labels)
    (p.ratioDomain N labels) (p.ratioDomain_open N labels) (p.ratioDomain_reference N labels)
    p.epsilon p.distortionH p.distortionB p.distortionJ p.epsilon_positive p.distortionH_nonnegative
    (IntrinsicDistortionContinuity.continuousOn_ratio m.maps Fiber p.differential p.unstable
      p.maps_continuous m.weight p.actual_weight_continuous p.weight_nonnegative
      p.epsilon p.epsilon_positive N (p.ratioDomain N labels) _ (p.jacobian_closed_continuous N labels))
    (p.error N labels)
    (p.deterministic_increment N labels) (p.deterministic_sum N labels) (p.deterministic_jacobian N labels)) :=
  IntrinsicNearbyPrincipalCoefficient.exists_uniform_separate_bound m.maps Fiber p.differential
    p.stable p.unstable m.weight p.weight_nonnegative N p.T p.K p.hK
    (ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels)
    (ClosedAtlasWordCylinders.cylinder_closed _ _ p.maps_continuous N labels)
    (p.ratioDomain N labels) (p.ratioDomain_open N labels) (p.ratioDomain_reference N labels)
    p.epsilon p.distortionH p.distortionB p.distortionJ p.epsilon_positive p.distortionH_nonnegative
    (IntrinsicDistortionContinuity.continuousOn_ratio m.maps Fiber p.differential p.unstable
      p.maps_continuous m.weight p.actual_weight_continuous p.weight_nonnegative
      p.epsilon p.epsilon_positive N (p.ratioDomain N labels) _ (p.jacobian_closed_continuous N labels))
    (p.error N labels)
    (p.deterministic_increment N labels) (p.deterministic_sum N labels) (p.deterministic_jacobian N labels)

private def narrowedControls (N : ℕ) (labels : Fin (N + 1) → m.localization.indices) :=
  (p.controls N labels).narrow (Classical.choose (p.nearby m N labels))
    (Classical.choose_spec (p.nearby m N labels)).1
    (Classical.choose_spec (p.nearby m N labels)).2.1

omit [∀ k, CompleteSpace (LocalReg k)] in
private theorem hyperbolicity_continuous (N : ℕ) (i : I N) :
    ContinuousOn (IntrinsicPrincipalSuprema.hyperbolicity m.maps Fiber p.differential
      p.stable p.unstable N p.t p.s) (p.chart N i) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact ((continuousOn_iff_continuous_domRestrict.mp (p.stable_continuous N i)).rpow_const
    (fun _ => Or.inr p.ht)).max
      ((continuousOn_iff_continuous_domRestrict.mp (p.inverse_continuous N i)).rpow_const
        (fun _ => Or.inr (neg_nonneg.mpr p.hs)))

set_option maxHeartbeats 1600000 in
def constructed : PhysicalManifoldPreControlSources.Data m (Fiber := Fiber) (I := I) where
  r := p.r
  regularity_gt_one := p.regularity_gt_one
  T := p.T
  maps := p.maps
  maps_eq := p.maps_eq
  control_out := p.control_out
  control_inp := p.control_inp
  control_cutoff := p.control_cutoff
  control_weight := p.control_weight
  control_source := p.control_source
  control_target := p.control_target
  control_order := p.control_order
  K := p.K
  hK := p.hK
  core_in_live := p.core_in_live
  control_survivors := p.control_survivors
  control_backward := p.control_backward
  differential := p.differential
  envelope := p.envelope
  stable := p.stable
  unstable := p.unstable
  t := p.t
  s := p.s
  ht := p.ht
  hs := p.hs
  admissible := p.admissible
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
  Qpressure := p.Qpressure
  Cmic := p.Cmic
  hCmic := p.hCmic
  pressure := p.pressure
  capture := fun N _ v => (FiniteSmoothCapturePartition.data (E := E)
    (fiber p.K (p.surviving N) (fun _ : Fin N => p.T))
    (fiber_isCompact p.hK (p.closed N) _) v).capture
  capture_open := fun N _ v => (FiniteSmoothCapturePartition.data (E := E)
    (fiber p.K (p.surviving N) (fun _ : Fin N => p.T))
    (fiber_isCompact p.hK (p.closed N) _) v).open_capture
  capture_reference := fun N _ v hv _ _ hcover =>
    (FiniteSmoothCapturePartition.data (E := E)
      (fiber p.K (p.surviving N) (fun _ : Fin N => p.T))
      (fiber_isCompact p.hK (p.closed N) _) v).reference hv hcover
  pairMember := p.pairMember
  principal := p.principal
  remainder := p.remainder
  nonneg := p.nonneg
  controls := p.narrowedControls m
  Cchart := p.Ccoordinate * (Real.exp ((p.distortionH / p.epsilon) * p.distortionB + p.distortionJ) + 1)
  hCchart := mul_nonneg p.hCcoordinate (by positivity)
  positive := by
    have hp := mul_pos p.positive
      (show 0 < Real.exp ((p.distortionH / p.epsilon) * p.distortionB + p.distortionJ) + 1 by positivity)
    convert hp using 1; ring
  source := by
    intro N c v parameters word hvalid hparams hv hvcompact hvchart hcover hcapture
    have hvalid0 : word ∈ ChartWordControlFamily.valid p.controls N := by
      intro labels j
      exact (hvalid labels j).1
    have hparams0 : ChartWordControlFamily.predicate p.controls N parameters word := hparams
    have hraw := p.source N c v parameters word hvalid0 hparams0 hv hvcompact hvchart hcover hcapture
    refine ⟨?_, hraw.2⟩
    intro i j
    refine (hraw.1 i j).trans ?_
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ p.hCcoordinate
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    let labels := p.cylinderLabel N k.val
    have hw : ∀ j, word j ∈ Classical.choose (p.nearby m N labels) :=
      fun j => (hvalid labels j).2
    have hsub : fiber p.K (univ ×ˢ closure (v k)) word ⊆ fiber p.K
        (ClosedAtlasWordCylinders.cylinder (fun i : m.localization.indices => m.atlas i) m.maps N labels) word := by
      intro x hx
      exact ⟨hx.1, p.chart_in_closed N k.val (hvchart k x hx.2.2)⟩
    have hmap : MapsTo (fun x => (word, x)) (fiber p.K (univ ×ˢ closure (v k)) word) (p.chart N k.val) :=
      fun x hx => hvchart k x hx.2.2
    have he : ContinuousOn (fun x => IntrinsicPrincipalSuprema.originalWeight m.maps (fun q => m.weight q + p.epsilon) N (word, x)) (fiber p.K (univ ×ˢ closure (v k)) word) := by
      rw [← p.envelope_identity]
      exact (p.weight_continuous N k.val).comp (continuous_const.prodMk continuous_id).continuousOn hmap
    have hbound := (Classical.choose_spec (p.nearby m N labels)).2.2 word hw
      (univ ×ˢ closure (v k)) (isClosed_univ.prod isClosed_closure) hsub p.t p.s
      ((ActualWordWeightContinuity.continuous_weight m.maps p.maps_continuous m.weight
        p.actual_weight_continuous N).comp (continuous_const.prodMk continuous_id)).continuousOn
      he
      ((p.jacobian_continuous N k.val).comp (continuous_const.prodMk continuous_id).continuousOn hmap)
      ((p.hyperbolicity_continuous m N k.val).comp (continuous_const.prodMk continuous_id).continuousOn hmap)
    simpa only [← p.envelope_identity] using hbound

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldPreDistortionSources
