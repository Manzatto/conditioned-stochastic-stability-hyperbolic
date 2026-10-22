module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierBlock
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalytic
meta import Lean.LibrarySuggestions.Basic

/-! The two stages of the adapted tube carrier on one common setup: the strong
stage `(t,s)` with its block bound (D5) and one-step bound (D4), and the weak
stage `(t-loss,s-loss)` with its one-step bound, on a window that also lies
below the higher ordinary action window of order `a` (used by the noise
interpolation). -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "adapted_carrier_stages"

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

theorem carrierStage_margin {t s loss b₀ : ℝ} (margin : ∀ sign, BTLinkedDyadicWeights.exponent t s sign ≤ b₀)
    (nonneg : 0 ≤ loss) : ∀ sign, BTLinkedDyadicWeights.exponent (t - loss) (s - loss) sign ≤ b₀ := by
  intro sign
  cases sign
  · exact (sub_le_self _ nonneg).trans (margin false)
  · exact (sub_le_self _ nonneg).trans (margin true)

theorem carrierStage_lowered (t s loss : ℝ) :
    BTLinkedDyadicWeights.exponent (t - loss) (s - loss) =
      fun sign => BTLinkedDyadicWeights.exponent t s sign - loss := by
  funext sign
  cases sign <;> rfl

theorem carrierStage_facts {t s loss α : ℝ} (positiveLoss : 0 < loss) (lossT : loss < t)
    (negativeS : s < 0) (gap : t - s + loss < α) :
    0 < t - loss ∧ s - loss < 0 ∧ (t - loss) - (s - loss) + loss < α := by
  refine ⟨by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 3200000 in
theorem Maps.adapted_carrier_stages (μE : Measure system.EuclideanModel) [μE.IsAddHaarMeasure]
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
    {t s loss : ℝ} (positiveT : 0 < t) (negativeS : s < 0) (positiveLoss : 0 < loss)
    (gap : t - s + loss < α)
    (margin : ∀ sign, BTLinkedDyadicWeights.exponent t s sign ≤ b₀)
    {lossH : ℝ} (hH : 0 < lossH) (lossT : loss < t)
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
        (BTLinkedDyadicWeights.exponent t s) margin lossH loss hH positiveLoss η cap) L) ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     ∃ L : ℝ, 0 ≤ L ∧ PhysicalModelAnalytic.AnalyticBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
        (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap) L) ∧
    ∃ P : ℝ, ThermodynamicDefinitions.pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < Real.exp P ∧ ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 ≤ B ∧
    ∀ ε : ℝ≥0, ∀ hp : 0 < ε, ∀ hl : ε ≤ η, ∀ control : Fin N → cube (ι := ι) ε,
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     PhysicalModelUniformBounds.WordBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin lossH loss hH positiveLoss η cap)
      (List.ofFn fun k => letter atlas d hb₀ hb₀1 μE openW region F hr regularT forward b₀q hχg
          support η cap ε hp hl (control k))
      (ρ ^ N) B) := by
  classical
  -- Stage 0: the polarized chart-pair producer.
  choose μ positiveμ smallμ ν largeν A tubeCap positiveTube cutoff positiveCut cutWindow h6
    using Maps.adapted_polarized_carrier_rows F positiveα subunitα
      lower αq regularT backward atlas positiveStable radial cutoffs
  -- Stage 1: the finite adapted tube partition.
  choose tubes d captureD using atlas.exists_normalizedTube_partition positiveTube
  -- Stage 2: the strict collar inside the capture and its preimage.
  let ambient : Set M := d.capture ∩ (T : M → M) ⁻¹' d.capture
  have openAmbient : IsOpen ambient :=
    d.open_capture.inter (d.open_capture.preimage T.continuous)
  have coreAmbient : Λ ⊆ ambient := fun x hx => ⟨captureD hx, captureD (by
    rw [← b.hyperbolic.invariant]; exact mem_image_of_mem _ hx)⟩
  let rowFactor : ℝ := (A : ℝ) * (max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s)) * LeanShared.BTLinkedDyadicWeights.rowConstant t s)
  let collarA : ℝ := max ((Fintype.card tubes : ℝ) ^ 2 * rowFactor) 1
  have positiveCollarA : 0 < collarA := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  choose P pressureP ρ radius positiveρ belowP positiveRadius N positiveN aboveMinimum centers p
    captureP W openW coreW closureW ηc positiveηc ηcWindow stepCap nonnegativeStep collar
    using F.exists_strict_nativeCost_collar_with_step (J := tubes) hr b forward backward g
      weight positive d captureD positiveμ smallμ largeν positiveT negativeS collarA
      positiveCollarA.le ambient openAmbient coreAmbient 1
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
  -- Stage 6: one-letter rows (D4) with the collar's one-step cost cap.
  choose R1 R1nonneg rows1 using rowsAll 1 one_pos hb₀ hb₀1 b₀q t s loss positiveT negativeS
    positiveLoss gap margin stepCap nonnegativeStep
  let Smax : ℝ := ((A : ℝ) * ((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s)) *
      BTLinkedDyadicWeights.rowConstant t s) * max ((10*μ^1)^t) (((4*(ν⁻¹)^1)⁻¹)^s))) * stepCap
  have nonnegativeS : 0 ≤ Smax :=
    mul_nonneg (carrierBlock_coefficient_nonneg A positiveT negativeS (ν := ν) positiveμ 1)
      nonnegativeStep
  have letterRows : ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η → ∀ c : cube (ι := ι) ε,
      Rows atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin positiveLoss (F.family ε c.val)
        (fun x => χ x * g x) Smax R1 := by
    intro ε hε hl c
    let control : Fin 1 → cube (ι := ι) ε := fun _ => c
    have costBound := (collar ε hε (hl.trans ηCollar)
      (fun n => if h : n < 1 then control ⟨n, h⟩ else control ⟨0, one_pos⟩) χ absχ τ absτ).1
    have row := rows1 ε hε (hl.trans ηWindow) control costBound
      (capture 1 one_pos ε hε hl control)
    have larger := mul_le_mul_of_nonneg_left costBound
      (carrierBlock_coefficient_nonneg A positiveT negativeS (ν := ν) positiveμ 1)
    exact Rows.congr atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ margin positiveLoss
      (Rows.mono atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ margin positiveLoss
        row larger)
      (funext fun x => rfl) (funext fun m => Finset.prod_range_one _)
  -- Stage 6': one-letter rows of the weak stage (t-loss, s-loss).
  have stageFacts := carrierStage_facts positiveLoss lossT negativeS gap
  choose R1W R1Wnonneg rows1W using rowsAll 1 one_pos hb₀ hb₀1 b₀q (t - loss) (s - loss) loss
    stageFacts.1 stageFacts.2.1 positiveLoss stageFacts.2.2
    (carrierStage_margin margin positiveLoss.le) stepCap nonnegativeStep
  let SmaxW : ℝ := ((A : ℝ) * ((max ((2:ℝ)^(6*(t - loss))) ((2:ℝ)^(-7*(s - loss))) *
      BTLinkedDyadicWeights.rowConstant (t - loss) (s - loss)) *
      max ((10*μ^1)^(t - loss)) (((4*(ν⁻¹)^1)⁻¹)^(s - loss)))) * stepCap
  have nonnegativeSW : 0 ≤ SmaxW :=
    mul_nonneg (carrierBlock_coefficient_nonneg A stageFacts.1 stageFacts.2.1 (ν := ν) positiveμ 1)
      nonnegativeStep
  have letterRowsW : ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η → ∀ c : cube (ι := ι) ε,
      Rows atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
        (carrierStage_margin margin positiveLoss.le) positiveLoss (F.family ε c.val)
        (fun x => χ x * g x) SmaxW R1W := by
    intro ε hε hl c
    let control : Fin 1 → cube (ι := ι) ε := fun _ => c
    have costBound := (collar ε hε (hl.trans ηCollar)
      (fun n => if h : n < 1 then control ⟨n, h⟩ else control ⟨0, one_pos⟩) χ absχ τ absτ).1
    have row := rows1W ε hε (hl.trans ηWindow) control costBound
      (capture 1 one_pos ε hε hl control)
    have larger := mul_le_mul_of_nonneg_left costBound
      (carrierBlock_coefficient_nonneg A stageFacts.1 stageFacts.2.1 (ν := ν) positiveμ 1)
    exact Rows.congr atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ _ positiveLoss
      (Rows.mono atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ _ positiveLoss
        row larger)
      (funext fun x => rfl) (funext fun m => Finset.prod_range_one _)
  -- Stage 7: block rows (D5) with the strict-collar cost cap.
  let maxN : ℝ := max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s)
  have positiveMaxN : 0 < maxN := carrierBlock_max_pos positiveμ N
  have nonnegativeCapN : 0 ≤ ρ ^ N / (collarA * maxN) :=
    div_nonneg (pow_nonneg positiveρ.le _) (mul_pos positiveCollarA positiveMaxN).le
  choose RN RNnonneg rowsN using rowsAll N positiveN hb₀ hb₀1 b₀q t s loss positiveT negativeS
    positiveLoss gap margin (ρ ^ N / (collarA * maxN)) nonnegativeCapN
  refine ⟨tubeCap, tubes, d, W, openW, region, χ, hχg, support, η, positiveη, cap, capHigh,
    ?_, ?_, P, pressureP, ρ, positiveρ, belowP, N, positiveN, ∑ i : tubes, ∑ j : tubes, RN i j,
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => RNnonneg i j, ?_⟩
  · let := charts atlas
    let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
    exact ⟨_, PhysicalModelUniformBounds.oneStepConstant_nonneg _ Smax nonnegativeS _
      (fun i j => R1nonneg _ _), PhysicalModelAnalytic.analytic_of_estimates _ Smax _
      (fun i j => R1nonneg _ _) (letter_estimates atlas d hb₀ hb₀1 positiveStable radial
        cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin positiveLoss μE openW region F
        hr regularT forward b₀q hχg support lossH hH η cap positiveη Smax nonnegativeS R1
        letterRows)⟩
  · let := charts atlas
    let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
    exact ⟨_, PhysicalModelUniformBounds.oneStepConstant_nonneg _ SmaxW nonnegativeSW _
      (fun i j => R1Wnonneg _ _), PhysicalModelAnalytic.analytic_of_estimates _ SmaxW _
      (fun i j => R1Wnonneg _ _) (letter_estimates atlas d hb₀ hb₀1 positiveStable radial
        cutoffs.original (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
        (carrierStage_margin margin positiveLoss.le) positiveLoss μE openW region F
        hr regularT forward b₀q hχg support lossH hH η cap positiveη SmaxW nonnegativeSW R1W
        letterRowsW)⟩
  intro ε hp hl control
  have strict := (collar ε hp (hl.trans ηCollar)
    (fun n => if h : n < N then control ⟨n, h⟩ else control ⟨0, positiveN⟩) χ absχ τ absτ).2
  have facts := carrierBlock_cost_facts _ _ positiveCollarA positiveMaxN strict
  have row := rowsN ε hp (hl.trans ηWindow) control facts.2 (capture N positiveN ε hp hl control)
  have word := word_bound_of_rows' atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent t s) margin positiveLoss μE openW region F hr regularT forward
    b₀q hχg support lossH hH η cap positiveη Smax nonnegativeS R1 R1nonneg letterRows ε hp hl
    control _ (mul_nonneg (carrierBlock_coefficient_nonneg A positiveT negativeS (ν := ν) positiveμ
      N) facts.1) RN RNnonneg row
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact PhysicalModelUniformBounds.WordBound.mono _ word
    (carrierBlock_principal (le_max_left _ _) positiveMaxN.le facts.1 strict) le_rfl

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
