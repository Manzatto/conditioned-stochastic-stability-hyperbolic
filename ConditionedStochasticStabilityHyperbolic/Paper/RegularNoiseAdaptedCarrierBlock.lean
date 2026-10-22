module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedPolarizedChartPairTwoNorm
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseStrictNativeCostCollarStep
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCaptureWindow
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierBounds
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierRows
public import LeanShared.Analysis.ActualWordPrefixOrbit
public import LeanShared.Geometry.SmoothFractionalRegularity
public import LeanShared.Geometry.FractionalScalarMultiplication
public import LeanShared.Geometry.FiniteCaptureTerminalCutoffs
public import LeanShared.Geometry.SmoothWeightCutoff
meta import Lean.LibrarySuggestions.Basic

/-! D4 and D5 for the actual physical carrier on the adapted tube atlas.
The carrier weight is the killed weight `χ·g` (χ a smooth cutoff equal to one
on Λ, supported in the strict collar). Every constructed generator (every
positive-scale noise map, and the reference map) has one uniform strong bound;
every literal noise word of the strict-collar block length obeys the
completed two-norm block bound with principal factor `ρ^N`, `ρ < exp P`. -/

-- The theorem statement contains the whole carrier; exclude it from the
-- library-suggestion symbol-frequency export, which does not share subterms.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "adapted_carrier_block"

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

theorem carrierBlock_abs {x : ℝ} (h : 0 ≤ x ∧ x ≤ 1) : |x| ≤ 1 :=
  abs_le.mpr ⟨by linarith [h.1], h.2⟩

theorem carrierBlock_domain_nonneg {X : Type*} (K A : Set X) (f : X → ℝ) :
    0 ≤ PressureCoverRefinement.domainCoefficient K A f := by
  unfold PressureCoverRefinement.domainCoefficient
  by_cases hb : BddAbove ({0} ∪ f '' (K ∩ A))
  · exact le_csSup hb (Or.inl (mem_singleton 0))
  · rw [Real.sSup_of_not_bddAbove hb]

theorem carrierBlock_cost_facts {Y Lb J X : Type*} [Fintype Y] [Fintype Lb] [Fintype J]
    (K : Y → Set X) (f : Y → Lb → J → X → ℝ) {C m ρN : ℝ} (hC : 0 < C) (hm : 0 < m)
    (strict : C * m * (∑ y, ∑ l, ∑ j, PressureCoverRefinement.domainCoefficient (K y) univ (f y l j))
      < ρN) :
    0 ≤ (∑ y, ∑ l, ∑ j, PressureCoverRefinement.domainCoefficient (K y) univ (f y l j)) ∧
    (∑ y, ∑ l, ∑ j, PressureCoverRefinement.domainCoefficient (K y) univ (f y l j)) ≤
      ρN / (C * m) := by
  have nonneg : 0 ≤ (∑ y, ∑ l, ∑ j, PressureCoverRefinement.domainCoefficient (K y) univ (f y l j)) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      carrierBlock_domain_nonneg _ _ _
  refine ⟨nonneg, ?_⟩
  rw [le_div_iff₀ (mul_pos hC hm)]
  linarith

theorem carrierBlock_coefficient_nonneg (A : ℝ≥0) {t s : ℝ} (ht : 0 < t) (hs : s < 0)
    {μ ν : ℝ} (hμ : 0 < μ) (K : ℕ) :
    0 ≤ (A : ℝ) * ((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s)) * BTLinkedDyadicWeights.rowConstant t s) *
      max ((10*μ^K)^t) (((4*(ν⁻¹)^K)⁻¹)^s)) := by
  have row := BTLinkedDyadicWeights.rowConstant_positive t s ht hs
  have m1 : 0 ≤ max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s)) := le_max_of_le_left (by positivity)
  have m2 : 0 ≤ max ((10*μ^K)^t) (((4*(ν⁻¹)^K)⁻¹)^s) := le_max_of_le_left (by positivity)
  exact mul_nonneg A.2 (mul_nonneg (mul_nonneg m1 row.le) m2)

theorem carrierBlock_max_pos {t s μ ν : ℝ} (hμ : 0 < μ) (K : ℕ) :
    0 < max ((10*μ^K)^t) (((4*(ν⁻¹)^K)⁻¹)^s) :=
  lt_max_of_lt_left (by positivity)

theorem carrierBlock_principal {k a mx rc mN c C ρN : ℝ} (hC : k ^ 2 * (a * (mx * rc)) ≤ C)
    (hmN : 0 ≤ mN) (hc : 0 ≤ c) (strict : C * mN * c < ρN) :
    k ^ 2 * (a * ((mx * rc) * mN) * c) ≤ ρN := by
  have e : k ^ 2 * (a * ((mx * rc) * mN) * c) = (k ^ 2 * (a * (mx * rc))) * mN * c := by ring
  rw [e]
  exact le_of_lt (lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hmN) hc) strict)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M] [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
/-- A nonzero killed weight keeps the whole prefix orbit in the collar `W`;
the next noisy step then stays in the capture. -/
theorem carrierBlock_capture {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (χ g : M → ℝ)
    {W Pcap Dcap : Set M} (supportχ : tsupport χ ⊆ W) (inP : ∀ x ∈ W, x ∈ Pcap)
    {η w : ℝ≥0} (ηw : η ≤ w)
    (captureWin : ∀ ε : ℝ≥0, 0 < ε → ε ≤ w → ∀ control : cube (ι := ι) ε,
      ∀ x ∈ closure W, F.family ε control.val x ∈ Dcap)
    {Iβ : Type*} (beta : Iβ → M → ℝ) :
    ∀ (K : ℕ), 0 < K → ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η →
      ∀ control : Fin K → cube (ι := ι) ε, ∀ (i : Iβ) (m : M),
      beta i m * (∏ k ∈ Finset.range K,
        χ (CylinderPrincipalCoefficient.prefixOrbit
          (fun c : cube (ι := ι) ε => F.family ε c.val) control k m) *
        g (CylinderPrincipalCoefficient.prefixOrbit
          (fun c : cube (ι := ι) ε => F.family ε c.val) control k m)) ≠ 0 →
      m ∈ Pcap ∧ ∀ k : Fin K, CylinderPrincipalCoefficient.prefixOrbit
        (fun c : cube (ι := ι) ε => F.family ε c.val) control (k.val + 1) m ∈ Dcap := by
  intro K positiveK ε hε small control i m nonzero
  have factors := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul nonzero)
  have inside : ∀ k < K, CylinderPrincipalCoefficient.prefixOrbit
      (fun c : cube (ι := ι) ε => F.family ε c.val) control k m ∈ W := fun k hk =>
    supportχ (subset_tsupport _ (Function.mem_support.mpr
      (left_ne_zero_of_mul (factors k (Finset.mem_range.mpr hk)))))
  refine ⟨inP m (inside 0 positiveK), fun k => ?_⟩
  rw [CylinderPrincipalCoefficient.prefixOrbit, dite_eq_left_of_eq_true (eq_true k.isLt)]
  exact captureWin ε hε (small.trans ηw) (control k) _ (subset_closure (inside k.val k.isLt))

set_option maxHeartbeats 3200000 in
theorem Maps.adapted_carrier_block (μE : Measure system.EuclideanModel) [μE.IsAddHaarMeasure]
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
    {lossH : ℝ} (hH : 0 < lossH) :
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
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     ∃ L : ℝ, 0 ≤ L ∧ PhysicalModelUniformBounds.GeneratorBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin lossH loss hH positiveLoss η cap) L) ∧
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
  let η : ℝ≥0 := min (min (min window ηc) w) carrierBounds.window
  have positiveη : 0 < η := lt_min (lt_min (lt_min positiveWindow positiveηc) positiveW)
    carrierBounds.positive
  have cap : η ≤ carrierBounds.window := min_le_right _ _
  have ηWindow : η ≤ window := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have ηCollar : η ≤ ηc := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have ηCapture : η ≤ w := (min_le_left _ _).trans (min_le_right _ _)
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
  -- Stage 7: block rows (D5) with the strict-collar cost cap.
  let maxN : ℝ := max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s)
  have positiveMaxN : 0 < maxN := carrierBlock_max_pos positiveμ N
  have nonnegativeCapN : 0 ≤ ρ ^ N / (collarA * maxN) :=
    div_nonneg (pow_nonneg positiveρ.le _) (mul_pos positiveCollarA positiveMaxN).le
  choose RN RNnonneg rowsN using rowsAll N positiveN hb₀ hb₀1 b₀q t s loss positiveT negativeS
    positiveLoss gap margin (ρ ^ N / (collarA * maxN)) nonnegativeCapN
  refine ⟨tubeCap, tubes, d, W, openW, region, χ, hχg, support, η, positiveη, cap,
    generator_bound_of_rows atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent t s) margin positiveLoss μE openW region F hr regularT forward
      b₀q hχg support lossH hH η cap positiveη Smax nonnegativeS R1 R1nonneg letterRows,
    P, pressureP, ρ, positiveρ, belowP, N, positiveN, ∑ i : tubes, ∑ j : tubes, RN i j,
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => RNnonneg i j, ?_⟩
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
