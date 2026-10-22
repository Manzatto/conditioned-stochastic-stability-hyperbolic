module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierStages
meta import Lean.LibrarySuggestions.Basic

/-! The three stages of the adapted tube carrier on ONE common setup (tube
partition, collar, cutoff, window, pressure rate and block length):
the strong stage `B₀ = (t,s)`, the middle stage `B₁ = (t-δ,s-δ)` and the weak
stage `B₂ = (t-2δ,s-2δ)`. Both strong stages `B₀,B₁` get the block bound (D5)
with the same `ρ, N, B`, and all three get the one-step bound (D4). The weak
norm of `B₀` loses `2δ` and that of `B₁` loses `δ`, so both are read in `B₂`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "adapted_carrier_tower_stages"

public noncomputable section
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal Topology BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open AdaptedTubeUnitCarrierBounds

variable {E ι : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

/-- The numerical facts of the middle and weak stages. -/
theorem towerStage_facts {t s δ α : ℝ} (positiveδ : 0 < δ) (twoδ : δ + δ < t) (negativeS : s < 0)
    (gap : t - s + (δ + δ) < α) :
    0 < t - δ ∧ s - δ < 0 ∧ (t - δ) - (s - δ) + δ < α ∧
    0 < t - δ - δ ∧ s - δ - δ < 0 ∧ (t - δ - δ) - (s - δ - δ) + δ < α := by
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem towerStage_collar_pos (x y : ℝ) : 0 < max x (max y 1) :=
  lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans (le_max_right _ _))

/-- A block-length threshold beyond which `10 μ^N ≤ 1` and `4 ≤ ν^N`. -/
theorem towerStage_minimum {μ ν : ℝ} (hμ : 0 < μ) (smallμ : μ < 1) (largeν : 1 < ν) :
    ∃ m : ℕ, ∀ N, m ≤ N → 10 * μ ^ N ≤ 1 ∧ 4 ≤ ν ^ N := by
  obtain ⟨m₁, h₁⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 1/10 by norm_num) smallμ
  obtain ⟨m₂, h₂⟩ := pow_unbounded_of_one_lt (4:ℝ) largeν
  refine ⟨max m₁ m₂, fun N hN => ⟨?_, ?_⟩⟩
  · have : μ ^ N ≤ μ ^ m₁ := pow_le_pow_of_le_one hμ.le smallμ.le (le_trans (le_max_left _ _) hN)
    linarith
  · have : ν ^ m₂ ≤ ν ^ N := pow_le_pow_right₀ largeν.le (le_trans (le_max_right _ _) hN)
    linarith

theorem towerStage_max_le₀ {a c t s δ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 ≤ δ) :
    max (a ^ t) (c ^ s) ≤ max (a ^ (t - δ)) (c ^ s) :=
  max_le_max (Real.rpow_le_rpow_of_exponent_ge ha ha1 (by linarith)) le_rfl

theorem towerStage_max_le₁ {a c t s δ : ℝ} (hc : 1 ≤ c) (hδ : 0 ≤ δ) :
    max (a ^ (t - δ)) (c ^ (s - δ)) ≤ max (a ^ (t - δ)) (c ^ s) :=
  max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le hc (by linarith))

theorem towerStage_base_pos {μ : ℝ} (hμ : 0 < μ) (N : ℕ) : 0 < 10 * μ ^ N :=
  mul_pos (by norm_num) (pow_pos hμ N)

theorem towerStage_base_ge {ν : ℝ} (hν : 0 < ν) {N : ℕ} (h : 4 ≤ ν ^ N) :
    1 ≤ (4 * (ν⁻¹) ^ N)⁻¹ := by
  have hp : 0 < ν ^ N := pow_pos hν N
  have e : 4 * (ν⁻¹) ^ N = 4 / ν ^ N := by rw [inv_pow, div_eq_mul_inv]
  rw [e, inv_div]
  exact (one_le_div (by norm_num)).mpr h

theorem towerStage_strict {C m m' c ρN : ℝ} (hC : 0 ≤ C) (hm : m ≤ m') (hc : 0 ≤ c)
    (h : C * m' * c < ρN) : C * m * c < ρN :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hC) hc) h

set_option maxHeartbeats 3200000 in
theorem Maps.adapted_carrier_tower_stages (μE : Measure system.EuclideanModel)
    [μE.IsAddHaarMeasure]
    {r α q : ℝ} (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (αq : α < q) (hr : 1 ≤ r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (atlas : ChartAtlas system) (positiveStable : 0 < system.framing.stableDimension)
    (g : M → ℝ) (weight : Continuous g) (positive : ∀ x ∈ Λ, 0 < g x)
    (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    (radial : ConeDyadicSymbols.RadialCutoff)
    (cutoffs : ConstructedEnlargedConeSymbols.Cutoffs
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (ProjectionConeTransversality.cone system.euclideanSecondProjection
        (OneStepConePolarization.minusOpening system.rate)))
    {b₀ : ℝ} (hb₀ : 0 < b₀) (hb₀1 : b₀ < 1) (b₀q : b₀ < q)
    {t s δ : ℝ} (positiveT : 0 < t) (negativeS : s < 0) (positiveδ : 0 < δ) (twoδ : δ + δ < t)
    (gap : t - s + (δ + δ) < α)
    (margin : ∀ sign, BTLinkedDyadicWeights.exponent t s sign ≤ b₀)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q) :
    ∃ radiusT : ℝ, ∃ tubes : Finset atlas.NormalizedTubeIndex,
    ∃ d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : tubes => atlas.normalizedTube radiusT i.val),
    ∃ W : Set M, ∃ openW : IsOpen W, ∃ region : W ⊆ d.capture,
    ∃ χ : M → ℝ,
    ∃ hχg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q (fun x => χ x * g x),
    ∃ support : tsupport (fun x => χ x * g x) ⊆ W,
    ∃ η : ℝ≥0, ∃ _positiveη : 0 < η,
    ∃ cap : η ≤ (bounds atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support).window,
    ∃ _capHigh : η ≤ (bounds atlas d μE openW region ha ha1 F hr regularT forward haq hχg
      support).window,
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     ∃ L : ℝ, 0 ≤ L ∧ PhysicalModelAnalytic.AnalyticBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ
        (add_pos positiveδ positiveδ) η cap) L) ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     ∃ L : ℝ, 0 ≤ L ∧ PhysicalModelAnalytic.AnalyticBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap) L) ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     ∃ L : ℝ, 0 ≤ L ∧ PhysicalModelAnalytic.AnalyticBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ - δ) (s - δ - δ))
        (carrierStage_margin (carrierStage_margin margin positiveδ.le) positiveδ.le)
        δ δ positiveδ positiveδ η cap) L) ∧
    ∃ P : ℝ, ThermodynamicDefinitions.pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < Real.exp P ∧ ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 ≤ B ∧
    (∀ ε : ℝ≥0, ∀ hp : 0 < ε, ∀ hl : ε ≤ η, ∀ control : Fin N → cube (ι := ι) ε,
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     PhysicalModelUniformBounds.WordBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ
        (add_pos positiveδ positiveδ) η cap)
      (List.ofFn fun k => letter atlas d hb₀ hb₀1 μE openW region F hr regularT forward b₀q hχg
          support η cap ε hp hl (control k))
      (ρ ^ N) B)) ∧
    (∀ ε : ℝ≥0, ∀ hp : 0 < ε, ∀ hl : ε ≤ η, ∀ control : Fin N → cube (ι := ι) ε,
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     PhysicalModelUniformBounds.WordBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap)
      (List.ofFn fun k => letter atlas d hb₀ hb₀1 μE openW region F hr regularT forward b₀q hχg
          support η cap ε hp hl (control k))
      (ρ ^ N) B)) := by
  classical
  have facts := towerStage_facts positiveδ twoδ negativeS gap
  have positive2δ : 0 < δ + δ := add_pos positiveδ positiveδ
  -- Stage 0: the polarized chart-pair producer.
  choose μ positiveμ smallμ ν largeν A tubeCap positiveTube cutoff positiveCut cutWindow h6
    using Maps.adapted_polarized_carrier_rows F positiveα subunitα
      lower αq regularT backward atlas positiveStable radial cutoffs
  -- Stage 1: the finite adapted tube partition.
  choose tubes d captureD using atlas.exists_normalizedTube_partition positiveTube
  -- Stage 2: the strict collar inside the capture and its preimage; one budget for both
  -- strong stages.
  let ambient : Set M := d.capture ∩ (T : M → M) ⁻¹' d.capture
  have openAmbient : IsOpen ambient :=
    d.open_capture.inter (d.open_capture.preimage T.continuous)
  have coreAmbient : Λ ⊆ ambient := fun x hx => ⟨captureD hx, captureD (by
    rw [← b.hyperbolic.invariant]; exact mem_image_of_mem _ hx)⟩
  let rowFactor0 : ℝ := (A : ℝ) * (max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s)) *
    LeanShared.BTLinkedDyadicWeights.rowConstant t s)
  let rowFactor1 : ℝ := (A : ℝ) * (max ((2:ℝ)^(6*(t - δ))) ((2:ℝ)^(-7*(s - δ))) *
    LeanShared.BTLinkedDyadicWeights.rowConstant (t - δ) (s - δ))
  let collarA : ℝ := max ((Fintype.card tubes : ℝ) ^ 2 * rowFactor0)
    (max ((Fintype.card tubes : ℝ) ^ 2 * rowFactor1) 1)
  have positiveCollarA : 0 < collarA := towerStage_collar_pos _ _
  obtain ⟨minimum, hminimum⟩ := towerStage_minimum positiveμ smallμ largeν
  choose P pressureP ρ radius positiveρ belowP positiveRadius N positiveN aboveMinimum centers p
    captureP W openW coreW closureW ηc positiveηc ηcWindow stepCap nonnegativeStep collar
    using F.exists_strict_nativeCost_collar_with_step (J := tubes) hr b forward backward g
      weight positive d captureD positiveμ smallμ largeν facts.1 negativeS collarA
      positiveCollarA.le ambient openAmbient coreAmbient minimum
  have bases := hminimum N aboveMinimum
  -- Stage 3: cutoffs.
  choose χ smoothχ boundsχ supportχ oneχ
    using SmoothWeightCutoff.exists_cutoff (E := E) Λ W b.hyperbolic.compact openW coreW
  choose τ smoothτ boundsτ supportτ oneτ
    using d.exists_terminal_cutoffs (fun i => atlas.normalizedTube_open tubeCap i.val)
  have hχg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q (fun x => χ x * g x) :=
    (FractionalManifoldRegularity.regular_of_smooth smoothχ (hb₀.trans b₀q).le).mul hg
  have support : tsupport (fun x => χ x * g x) ⊆ W := (tsupport_mul_subset_left).trans supportχ
  have region : W ⊆ d.capture := fun x hx => (closureW (subset_closure hx)).1.1.1
  have collarW : closure W ⊆ b.hyperbolic.normedAdaptedProjection.collar :=
    closureW.trans inter_subset_right
  -- Stage 4: the producer's window, the capture window and the carrier window.
  choose window positiveWindow windowCut rowsAll
    using h6 tubeCap le_rfl tubes d p χ g smoothχ.continuous weight hχg W supportχ collarW
      τ smoothτ supportτ oneτ
  choose w positiveW wWindow captureWin using F.exists_capture_window (K := closure W)
    (U := d.capture) isClosed_closure.isCompact d.open_capture (fun x hx => (closureW hx).1.1.2)
  let carrierBounds := bounds atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg support
  let highBounds := bounds atlas d μE openW region ha ha1 F hr regularT forward haq hχg support
  let η : ℝ≥0 := min (min (min (min window ηc) w) carrierBounds.window) highBounds.window
  have positiveη : 0 < η := lt_min (lt_min (lt_min (lt_min positiveWindow positiveηc) positiveW)
    carrierBounds.positive) highBounds.positive
  have capHigh : η ≤ highBounds.window := min_le_right _ _
  have cap : η ≤ carrierBounds.window := (min_le_left _ _).trans (min_le_right _ _)
  have ηWindow : η ≤ window := (min_le_left _ _).trans ((min_le_left _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _)))
  have ηCollar : η ≤ ηc := (min_le_left _ _).trans ((min_le_left _ _).trans
    ((min_le_left _ _).trans (min_le_right _ _)))
  have ηCapture : η ≤ w := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  -- Stage 5: the producer's capture hypothesis, for every block length.
  have capture := carrierBlock_capture F χ g supportχ
    (fun x hx => (closureW (subset_closure hx)).1.2) ηCapture captureWin d.beta
  have absχ : ∀ x, |χ x| ≤ 1 := fun x => carrierBlock_abs (boundsχ x)
  have absτ : ∀ j x, |τ j x| ≤ 1 := fun j x => carrierBlock_abs (boundsτ j x)
  -- Stage 6: one-letter rows (D4) of the three stages with the collar's one-step cost cap.
  let margin1 := carrierStage_margin margin positiveδ.le
  let margin2 := carrierStage_margin margin1 positiveδ.le
  choose R0 R0nonneg rows0 using rowsAll 1 one_pos hb₀ hb₀1 b₀q t s (δ + δ) positiveT negativeS
    positive2δ gap margin stepCap nonnegativeStep
  choose R1 R1nonneg rows1 using rowsAll 1 one_pos hb₀ hb₀1 b₀q (t - δ) (s - δ) δ facts.1
    facts.2.1 positiveδ facts.2.2.1 margin1 stepCap nonnegativeStep
  choose R2 R2nonneg rows2 using rowsAll 1 one_pos hb₀ hb₀1 b₀q (t - δ - δ) (s - δ - δ) δ
    facts.2.2.2.1 facts.2.2.2.2.1 positiveδ facts.2.2.2.2.2 margin2 stepCap nonnegativeStep
  let S0 : ℝ := ((A : ℝ) * ((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s)) *
      BTLinkedDyadicWeights.rowConstant t s) * max ((10*μ^1)^t) (((4*(ν⁻¹)^1)⁻¹)^s))) * stepCap
  let S1 : ℝ := ((A : ℝ) * ((max ((2:ℝ)^(6*(t - δ))) ((2:ℝ)^(-7*(s - δ))) *
      BTLinkedDyadicWeights.rowConstant (t - δ) (s - δ)) *
      max ((10*μ^1)^(t - δ)) (((4*(ν⁻¹)^1)⁻¹)^(s - δ)))) * stepCap
  let S2 : ℝ := ((A : ℝ) * ((max ((2:ℝ)^(6*(t - δ - δ))) ((2:ℝ)^(-7*(s - δ - δ))) *
      BTLinkedDyadicWeights.rowConstant (t - δ - δ) (s - δ - δ)) *
      max ((10*μ^1)^(t - δ - δ)) (((4*(ν⁻¹)^1)⁻¹)^(s - δ - δ)))) * stepCap
  have nonnegativeS0 : 0 ≤ S0 :=
    mul_nonneg (carrierBlock_coefficient_nonneg A positiveT negativeS (ν := ν) positiveμ 1)
      nonnegativeStep
  have nonnegativeS1 : 0 ≤ S1 :=
    mul_nonneg (carrierBlock_coefficient_nonneg A facts.1 facts.2.1 (ν := ν) positiveμ 1)
      nonnegativeStep
  have nonnegativeS2 : 0 ≤ S2 :=
    mul_nonneg (carrierBlock_coefficient_nonneg A facts.2.2.2.1 facts.2.2.2.2.1 (ν := ν)
      positiveμ 1) nonnegativeStep
  have letterRows0 : ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η → ∀ c : cube (ι := ι) ε,
      Rows atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin positive2δ (F.family ε c.val)
        (fun x => χ x * g x) S0 R0 := by
    intro ε hε hl c
    let control : Fin 1 → cube (ι := ι) ε := fun _ => c
    have costBound := (collar ε hε (hl.trans ηCollar)
      (fun n => if h : n < 1 then control ⟨n, h⟩ else control ⟨0, one_pos⟩) χ absχ τ absτ).1
    have row := rows0 ε hε (hl.trans ηWindow) control costBound
      (capture 1 one_pos ε hε hl control)
    have larger := mul_le_mul_of_nonneg_left costBound
      (carrierBlock_coefficient_nonneg A positiveT negativeS (ν := ν) positiveμ 1)
    exact Rows.congr atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ margin positive2δ
      (Rows.mono atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ margin positive2δ
        row larger)
      (funext fun x => rfl) (funext fun m => Finset.prod_range_one _)
  have letterRows1 : ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η → ∀ c : cube (ι := ι) ε,
      Rows atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) margin1 positiveδ (F.family ε c.val)
        (fun x => χ x * g x) S1 R1 := by
    intro ε hε hl c
    let control : Fin 1 → cube (ι := ι) ε := fun _ => c
    have costBound := (collar ε hε (hl.trans ηCollar)
      (fun n => if h : n < 1 then control ⟨n, h⟩ else control ⟨0, one_pos⟩) χ absχ τ absτ).1
    have row := rows1 ε hε (hl.trans ηWindow) control costBound
      (capture 1 one_pos ε hε hl control)
    have larger := mul_le_mul_of_nonneg_left costBound
      (carrierBlock_coefficient_nonneg A facts.1 facts.2.1 (ν := ν) positiveμ 1)
    exact Rows.congr atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ _ positiveδ
      (Rows.mono atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ _ positiveδ
        row larger)
      (funext fun x => rfl) (funext fun m => Finset.prod_range_one _)
  have letterRows2 : ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η → ∀ c : cube (ι := ι) ε,
      Rows atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ - δ) (s - δ - δ)) margin2 positiveδ
        (F.family ε c.val) (fun x => χ x * g x) S2 R2 := by
    intro ε hε hl c
    let control : Fin 1 → cube (ι := ι) ε := fun _ => c
    have costBound := (collar ε hε (hl.trans ηCollar)
      (fun n => if h : n < 1 then control ⟨n, h⟩ else control ⟨0, one_pos⟩) χ absχ τ absτ).1
    have row := rows2 ε hε (hl.trans ηWindow) control costBound
      (capture 1 one_pos ε hε hl control)
    have larger := mul_le_mul_of_nonneg_left costBound
      (carrierBlock_coefficient_nonneg A facts.2.2.2.1 facts.2.2.2.2.1 (ν := ν) positiveμ 1)
    exact Rows.congr atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ _ positiveδ
      (Rows.mono atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ _ positiveδ
        row larger)
      (funext fun x => rfl) (funext fun m => Finset.prod_range_one _)
  -- Stage 7: block rows (D5) of both strong stages with the strict-collar cost cap.
  let maxN0 : ℝ := max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s)
  let maxN1 : ℝ := max ((10*μ^N)^(t - δ)) (((4*(ν⁻¹)^N)⁻¹)^(s - δ))
  let maxC : ℝ := max ((10*μ^N)^(t - δ)) (((4*(ν⁻¹)^N)⁻¹)^s)
  have positiveMaxC : 0 < maxC := carrierBlock_max_pos positiveμ N
  have maxLe0 : maxN0 ≤ maxC :=
    towerStage_max_le₀ (towerStage_base_pos positiveμ N) bases.1 positiveδ.le
  have maxLe1 : maxN1 ≤ maxC :=
    towerStage_max_le₁ (towerStage_base_ge (lt_trans zero_lt_one largeν) bases.2) positiveδ.le
  have positiveMaxN0 : 0 < maxN0 := carrierBlock_max_pos positiveμ N
  have positiveMaxN1 : 0 < maxN1 := carrierBlock_max_pos positiveμ N
  have nonnegativeCapN0 : 0 ≤ ρ ^ N / (collarA * maxN0) :=
    div_nonneg (pow_nonneg positiveρ.le _) (mul_pos positiveCollarA positiveMaxN0).le
  have nonnegativeCapN1 : 0 ≤ ρ ^ N / (collarA * maxN1) :=
    div_nonneg (pow_nonneg positiveρ.le _) (mul_pos positiveCollarA positiveMaxN1).le
  choose RN0 RN0nonneg rowsN0 using rowsAll N positiveN hb₀ hb₀1 b₀q t s (δ + δ) positiveT
    negativeS positive2δ gap margin (ρ ^ N / (collarA * maxN0)) nonnegativeCapN0
  choose RN1 RN1nonneg rowsN1 using rowsAll N positiveN hb₀ hb₀1 b₀q (t - δ) (s - δ) δ facts.1
    facts.2.1 positiveδ facts.2.2.1 margin1 (ρ ^ N / (collarA * maxN1)) nonnegativeCapN1
  refine ⟨tubeCap, tubes, d, W, openW, region, χ, hχg, support, η, positiveη, cap, capHigh,
    ?_, ?_, ?_, P, pressureP, ρ, positiveρ, belowP, N, positiveN,
    max (∑ i : tubes, ∑ j : tubes, RN0 i j) (∑ i : tubes, ∑ j : tubes, RN1 i j),
    le_max_of_le_left (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => RN0nonneg i j),
    ?_, ?_⟩
  · let := charts atlas
    let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
    exact ⟨_, PhysicalModelUniformBounds.oneStepConstant_nonneg _ S0 nonnegativeS0 _
      (fun i j => R0nonneg _ _), PhysicalModelAnalytic.analytic_of_estimates _ S0 _
      (fun i j => R0nonneg _ _) (letter_estimates atlas d hb₀ hb₀1 positiveStable radial
        cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin positive2δ μE openW region F
        hr regularT forward b₀q hχg support δ positiveδ η cap positiveη S0 nonnegativeS0 R0
        letterRows0)⟩
  · let := charts atlas
    let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
    exact ⟨_, PhysicalModelUniformBounds.oneStepConstant_nonneg _ S1 nonnegativeS1 _
      (fun i j => R1nonneg _ _), PhysicalModelAnalytic.analytic_of_estimates _ S1 _
      (fun i j => R1nonneg _ _) (letter_estimates atlas d hb₀ hb₀1 positiveStable radial
        cutoffs.original (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) margin1 positiveδ μE
        openW region F hr regularT forward b₀q hχg support δ positiveδ η cap positiveη S1
        nonnegativeS1 R1 letterRows1)⟩
  · let := charts atlas
    let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
    exact ⟨_, PhysicalModelUniformBounds.oneStepConstant_nonneg _ S2 nonnegativeS2 _
      (fun i j => R2nonneg _ _), PhysicalModelAnalytic.analytic_of_estimates _ S2 _
      (fun i j => R2nonneg _ _) (letter_estimates atlas d hb₀ hb₀1 positiveStable radial
        cutoffs.original (BTLinkedDyadicWeights.exponent (t - δ - δ) (s - δ - δ)) margin2
        positiveδ μE openW region F hr regularT forward b₀q hχg support δ positiveδ η cap
        positiveη S2 nonnegativeS2 R2 letterRows2)⟩
  · intro ε hp hl control
    have strictC := (collar ε hp (hl.trans ηCollar)
      (fun n => if h : n < N then control ⟨n, h⟩ else control ⟨0, positiveN⟩) χ absχ τ absτ).2
    have costC := carrierBlock_cost_facts _ _ positiveCollarA positiveMaxC strictC
    have strict := towerStage_strict positiveCollarA.le maxLe0 costC.1 strictC
    have costFacts := carrierBlock_cost_facts _ _ positiveCollarA positiveMaxN0 strict
    have row := rowsN0 ε hp (hl.trans ηWindow) control costFacts.2
      (capture N positiveN ε hp hl control)
    have word := word_bound_of_rows' atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent t s) margin positive2δ μE openW region F hr regularT forward
      b₀q hχg support δ positiveδ η cap positiveη S0 nonnegativeS0 R0 R0nonneg letterRows0 ε hp hl
      control _ (mul_nonneg (carrierBlock_coefficient_nonneg A positiveT negativeS (ν := ν)
        positiveμ N) costFacts.1) RN0 RN0nonneg row
    let := charts atlas
    let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
    exact PhysicalModelUniformBounds.WordBound.mono _ word
      (carrierBlock_principal (le_max_left _ _) positiveMaxN0.le costFacts.1 strict)
      (le_max_left _ _)
  · intro ε hp hl control
    have strictC := (collar ε hp (hl.trans ηCollar)
      (fun n => if h : n < N then control ⟨n, h⟩ else control ⟨0, positiveN⟩) χ absχ τ absτ).2
    have costC := carrierBlock_cost_facts _ _ positiveCollarA positiveMaxC strictC
    have strict := towerStage_strict positiveCollarA.le maxLe1 costC.1 strictC
    have costFacts := carrierBlock_cost_facts _ _ positiveCollarA positiveMaxN1 strict
    have row := rowsN1 ε hp (hl.trans ηWindow) control costFacts.2
      (capture N positiveN ε hp hl control)
    have word := word_bound_of_rows' atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) margin1 positiveδ μE openW region F hr
      regularT forward b₀q hχg support δ positiveδ η cap positiveη S1 nonnegativeS1 R1 R1nonneg
      letterRows1 ε hp hl control _ (mul_nonneg (carrierBlock_coefficient_nonneg A facts.1
        facts.2.1 (ν := ν) positiveμ N) costFacts.1) RN1 RN1nonneg row
    let := charts atlas
    let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
    exact PhysicalModelUniformBounds.WordBound.mono _ word
      (carrierBlock_principal ((le_max_left _ _).trans (le_max_right _ _)) positiveMaxN1.le
        costFacts.1 strict) (le_max_right _ _)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
