module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedPolarizedTubePieceTwoNorm
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseChartPairPieceDecomposition
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoisePieceNativeCost
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseWordEncodings
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseTerminalAmplitudeHolder
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeTerminalPhysicalOutput
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeAmplitudeSupport
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeAdmissibility

/-! The two-norm bound for one adapted-tube chart pair and one actual noisy
word. The literal chart-pair transfer is reconstructed as the finite sum of
its pieces (pressure centre, beta word with first label the output chart,
independent terminal slot equal to the input chart). Each piece receives its
closed native output and the producer's native two-norm row; its principal
cost is its own strict-collar coefficient. The principal coefficient is the
whole strict-collar sum, and the weak remainder depends only on the fixed
block, a uniform cost cap and the chart pair. -/
public noncomputable section
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal SchwartzMap BoundedContinuousFunction Topology BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
open LeanShared.OrthogonalRateGlobalWordFakeLeaves
open LeanShared.OrthogonalProductCoordinates
open AllFakeLeafModel BTLinkedDyadicWeights PressureCoverRefinement

universe uZ uL uK

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem polarizedTubeLocalSupport_compact (atlas : ChartAtlas system) {radius : ℝ}
    {tubes : Finset atlas.NormalizedTubeIndex}
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : tubes => atlas.normalizedTube radius i.val)) (i : tubes) :
    IsCompact (ChartLocalization.localSupport (atlas.normalizedTubeChart i.val)
      (fun m => (d.beta i m : ℂ))) :=
  ChartLocalization.localSupport_isCompact (atlas.normalizedTubeChart i.val)
    (fun m => (d.beta i m : ℂ))
    ((tsupport_comp_subset Complex.ofReal_zero (d.beta i)).trans
      ((d.support i).trans (fun _ hx => hx.1))) (HasCompactSupport.of_compactSpace _)

set_option maxHeartbeats 6400000 in
theorem Maps.adapted_polarized_chart_pair_two_norm (μE : Measure E) [μE.IsAddHaarMeasure] {r α q : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (αq : α < q)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (atlas : ChartAtlas system) (positiveStable : 0 < system.framing.stableDimension)
    (outputRadial : ConeDyadicSymbols.RadialCutoff)
    (outputAngle : ConeDyadicSymbols.AngularCutoff
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (ProjectionConeTransversality.cone system.euclideanSecondProjection
        (OneStepConePolarization.minusOpening system.rate))) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∃ ν : ℝ, 1 < ν ∧ ∃ A : ℝ≥0,
    ∃ tubeCap : ℝ, 0 < tubeCap ∧ ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∀ radiusT : ℝ, radiusT ≤ tubeCap → ∀ tubes : Finset atlas.NormalizedTubeIndex,
      ∀ d : FiniteSmoothCapturePartition.Data (E := E) Λ
        (fun i : tubes => atlas.normalizedTube radiusT i.val),
      ∀ {Y : Type} [Fintype Y] {Kp : Set M} {vp : Y → Set M}
        (p : FiniteSmoothCapturePartition.Data (E := E) Kp vp),
      ∀ χ g : M → ℝ, Continuous χ → Continuous g →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q (fun x => χ x * g x) →
      ∀ W : Set M, tsupport χ ⊆ W → closure W ⊆ b.hyperbolic.normedAdaptedProjection.collar →
      ∀ τ : tubes → M → ℝ, (∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ)) ∞ (τ j)) →
        (∀ j, tsupport (τ j) ⊆ atlas.normalizedTube radiusT j.val) →
        (∀ j x, x ∈ tsupport (d.beta j) → τ j x = 1) →
      ∃ window : ℝ≥0, 0 < window ∧ window ≤ cutoff ∧
      ∀ N : ℕ, ∀ positiveN : 0 < N,
      ∀ {Z : Type uZ} {ιleaf : Type uL} {κfreq : Type uK}, ∀ [Finite Z], ∀ [Fintype ιleaf],
        ∀ [DecidableEq ιleaf], ∀ [Fintype κfreq],
      ∀ (_ambientBasis : OrthonormalBasis κfreq ℝ system.EuclideanModel)
      (planes : Z → Submodule ℝ system.EuclideanModel) (plus : Z → Set system.EuclideanModel)
      (cone : ∀ i, AllFakeLeafModel.ConeData (planes i) (plus i))
      (coordinates : ∀ i, EuclideanSpace ℝ ιleaf ≃ₗᵢ[ℝ] planes i)
      (basis : ∀ i, OrthonormalBasis ιleaf ℝ (planes i)) (o : Z),
      planes o = firstPlane system.euclideanDimension →
      plus o = ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2) →
      ∀ {inputMinus : Set system.EuclideanModel} (inputRadial : ConeDyadicSymbols.RadialCutoff)
      (inputCutoffs : ConstructedEnlargedConeSymbols.Cutoffs (plus o) inputMinus)
      {b₀ : ℝ} (hb₀ : 0 < b₀) (hb₀1 : b₀ < 1), b₀ < q →
      ∀ (t s loss : ℝ), 0 < t → s < 0 → ∀ hLoss : 0 ≤ loss, t-s+loss < α →
      ∀ margin : (∀ sign, exponent t s sign ≤ b₀),
      ∀ costCap : ℝ, 0 ≤ costCap →
      ∃ remainder : tubes → tubes → ℝ, (∀ i j, 0 ≤ remainder i j) ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ window →
      ∀ control : Fin N → cube (ι := ι) ε,
      let points := fun (m : M) (k : ℕ) => CylinderPrincipalCoefficient.prefixOrbit
        (fun c : cube (ι := ι) ε => F.family ε c.val) control k m
      let killed := fun m => ∏ k ∈ Finset.range N, χ (points m k) * g (points m k)
      let maps := fun n : ℕ => F.family ε
        (if h : n < N then control ⟨n, h⟩ else control ⟨0, positiveN⟩).val
      let cost := ∑ y : Y, ∑ labels : Fin (N+1) → tubes, ∑ j : tubes,
        domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
          (fun x => |τ j (FiniteJetComposition.word maps N x)| *
            nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x * g x) maps N labels x)
      cost ≤ costCap →
      (∀ i m, d.beta i m * killed m ≠ 0 →
        m ∈ p.capture ∧ ∀ k : Fin N, points m (k.val+1) ∈ d.capture) →
      ∀ i j : tubes,
      ∀ u : SchwartzJetSpace.supportedCore (ChartLocalization.localSupport
        (atlas.normalizedTubeChart j.val) (fun m => (d.beta j m : ℂ))),
      ∃ output : EuclideanSmoothHolderCore.space (polarizedTubeLocalSupport_compact atlas d i).closure hb₀ hb₀1,
        (∀ z, EuclideanSmoothHolderCore.physical (polarizedTubeLocalSupport_compact atlas d i).closure hb₀ hb₀1
          output z = ChartPairTransfer.pair (atlas.normalizedTubeChart i.val)
            (atlas.normalizedTubeChart j.val) (fun m => (d.beta i m : ℂ))
            (CylinderPrincipalCoefficient.prefixOrbit
              (fun c : cube (ι := ι) ε => F.family ε c.val) control N) killed u.val z) ∧
        ‖CompactHolderPhysicalBlocks.realize (volume : Measure (EuclideanSpace ℝ ιleaf))
          (GraphJacobian.densityBound_nonneg (ι := ιleaf) (Heterogeneous.commonSlope planes plus cone))
          (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis o) outputRadial
          outputAngle (polarizedTubeLocalSupport_compact atlas d i) hb₀ hb₀1 (exponent t s) margin output‖ ≤
        ((A : ℝ) * ((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*
            max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s)) * cost) *
          ‖AllFakeLeafHolderCoreBounds.coreBlocks planes plus cone coordinates basis
            inputRadial inputCutoffs.original (polarizedTubeLocalSupport_compact atlas d j) hb₀ hb₀1
            (exponent t s) margin o u‖ +
        remainder i j *
          ‖AllFakeLeafHolderCoreBounds.coreBlocks planes plus cone coordinates basis
            inputRadial inputCutoffs.original (polarizedTubeLocalSupport_compact atlas d j) hb₀ hb₀1
            (fun sign => exponent t s sign-loss)
            (fun sign => (sub_le_self _ hLoss).trans (margin sign)) o u‖ := by
  classical
  have regularity : 1 ≤ r := by linarith
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using regularity)
  have deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T :=
    regularT.differentiable.of_le (by exact_mod_cast order)
  have pieceT := Maps.adapted_polarized_tube_piece_two_norm.{uZ, uL, uK, _, _, _} F (b := b) (system := system)
      positiveα subunitα lower regularT backward atlas positiveStable outputRadial outputAngle
  rcases pieceT with ⟨μ,positiveμ,contractingμ,ν,expandingν,A,tubeCap,positiveTubeCap,
    η,positiveη,cutoff,positiveCutoff,cap,family⟩
  obtain ⟨radiusA,positiveRadiusA,belowRadiusA,noiseA,positiveNoiseA,belowNoiseA,admissibility⟩ :=
    F.adapted_normalizedTube_admissibility atlas positiveη positiveTubeCap
  refine ⟨μ,positiveμ,contractingμ,ν,expandingν,A,radiusA,positiveRadiusA,
    min cutoff noiseA,lt_min positiveCutoff positiveNoiseA,(min_le_left _ _).trans cap,?_⟩
  intro radiusT smallT tubes d Y _ Kp vp p χ g continuousχ continuousg regularKilled W supportχ collar
    τ smoothτ supportτ oneτ
  have smoothτC (j : tubes) : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (fun m => (τ j m : ℂ)) :=
    Complex.ofRealCLM.contMDiff.comp (smoothτ j)
  have smoothPressureC (y : Y) : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (fun m => (p.beta y m : ℂ)) :=
    Complex.ofRealCLM.contMDiff.comp (p.smooth y)
  have holderT := F.adapted_tube_source_terminal_amplitude_holder μE regularity deterministic atlas d
      positiveα subunitα αq regularKilled (fun j m => (τ j m : ℂ)) smoothτC
      (fun y m => (p.beta y m : ℂ)) smoothPressureC
  obtain ⟨ηH, holderT⟩ := holderT
  obtain ⟨positiveηH, belowηH, B, C, nonnegativeB, nonnegativeC, holder⟩ := holderT
  refine ⟨min (min cutoff noiseA) ηH,lt_min (lt_min positiveCutoff positiveNoiseA) positiveηH,
    min_le_left _ _,?_⟩
  intro N positiveN Z ιleaf κfreq _ _ _ _ ambientBasis planes plus cone coordinates basis o
    planeSame plusSame inputMinus inputRadial inputCutoffs b₀ hb₀ hb₀1 hb₀q t s loss ht hs hLoss gap
    margin costCap nonnegativeCap
  have nonnegativeG : 0 ≤ C * B ^ N := mul_nonneg nonnegativeC (pow_nonneg nonnegativeB N)
  have perJ (j : tubes) := family radiusT (smallT.trans belowRadiusA) tubes N positiveN ambientBasis planes
    plus cone coordinates basis o planeSame plusSame inputRadial inputCutoffs
    (tubeAmplitudeSupport_compact atlas d) nonnegativeG nonnegativeG (polarizedTubeLocalSupport_compact atlas d j)
    hb₀ hb₀1 t s loss ht hs hLoss gap margin
  choose frequencyCutoff rem rows using perJ
  have gapPositive : 0 < α - (t - s + loss) := by linarith
  have smallPower : (2:ℝ) ^ (-(α - (t - s + loss))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos one_le_two (neg_nonpos.mpr gapPositive.le)
  have nonnegativeGeometric : 0 ≤ 2 * (1 - (2:ℝ) ^ (-(α - (t - s + loss))))⁻¹ :=
    mul_nonneg zero_le_two (inv_nonneg.mpr (sub_nonneg.mpr smallPower))
  let weakCoefficient := fun j : tubes => (rem j : ℝ) * (2 * (1 - (2:ℝ) ^ (-(α - (t - s + loss))))⁻¹) +
    ((A : ℝ) * costCap) * (2 * (((frequencyCutoff j + 1 : ℕ) : ℝ) *
      (2:ℝ) ^ ((t - s + loss) * (((frequencyCutoff j + 1 : ℕ) : ℝ)))))
  have nonnegativeWeak (j : tubes) : 0 ≤ weakCoefficient j := by
    apply add_nonneg (mul_nonneg (rem j).coe_nonneg nonnegativeGeometric)
    apply mul_nonneg (mul_nonneg A.coe_nonneg nonnegativeCap)
    positivity
  refine ⟨fun i j => ∑ _y : Y, ∑ _labels : Fin N → tubes, weakCoefficient j,
    fun i j => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => nonnegativeWeak j,?_⟩
  intro ε hp hw control points killed maps cost hcost capture i j u
  have hwPiece : ε ≤ cutoff := hw.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hwAdm : ε ≤ noiseA := hw.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hwHolder : ε ≤ ηH := hw.trans (min_le_right _ _)
  have hwWindow : ε ≤ F.window := hwPiece.trans cap
  have continuousMaps (c : cube (ι := ι) ε) : Continuous (F.family ε c.val) :=
    (F.map_regular ε hp hwWindow c).differentiable.continuous
  have continuousPoints (k : ℕ) : Continuous (fun m => points m k) := by
    induction k with
    | zero => exact continuous_id
    | succ k ih =>
      by_cases hk : k < N
      · simpa only [points, CylinderPrincipalCoefficient.prefixOrbit, dite_eq_left hk,
          Function.comp_def] using (continuousMaps (control ⟨k,hk⟩)).comp ih
      · simpa only [points, CylinderPrincipalCoefficient.prefixOrbit, dite_eq_right hk] using ih
  let K := (max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s)
  let strong := ‖AllFakeLeafHolderCoreBounds.coreBlocks planes plus cone coordinates basis
    inputRadial inputCutoffs.original (polarizedTubeLocalSupport_compact atlas d j) hb₀ hb₀1
    (exponent t s) margin o u‖
  let weak := ‖AllFakeLeafHolderCoreBounds.coreBlocks planes plus cone coordinates basis
    inputRadial inputCutoffs.original (polarizedTubeLocalSupport_compact atlas d j) hb₀ hb₀1
    (fun sign => exponent t s sign-loss)
    (fun sign => (sub_le_self _ hLoss).trans (margin sign)) o u‖
  let chartI := atlas.normalizedTubeChart i.val
  let chartJ := atlas.normalizedTubeChart j.val
  let native := fun m => points m N
  let input := fun z => if native (chartI.symm z) ∈ chartJ.source then
    u.val (chartJ (native (chartI.symm z))) else 0
  let pieceCutoff := fun (y : Y) (ℓ : Fin N → tubes) (m : M) => (p.beta y m : ℂ) *
    (FiniteSmoothCapturePartition.wordCutoff d (fun k : Fin (N+1) => points m k.val)
      (Fin.cons i ℓ) : ℂ)
  let pieceAmplitude := fun m => (killed m : ℂ) * (τ j (native m) : ℂ)
  let pieceCost := fun (y : Y) (ℓ : Fin N → tubes) =>
    domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
      (fun x => |τ j (FiniteJetComposition.word maps N x)| *
        nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x * g x) maps N
          (Fin.cons i ℓ) x)
  have terminal : ∀ x ∈ chartJ.source, u.val (chartJ x) ≠ 0 → (τ j x : ℂ) = 1 := by
    intro x source nonzero
    have inside : chartJ x ∈ ChartLocalization.localSupport chartJ (fun m => (d.beta j m : ℂ)) := by
      by_contra outside
      exact nonzero (u.property _ outside)
    obtain ⟨x', member, same⟩ := inside
    have source' : x' ∈ chartJ.source :=
      ((tsupport_comp_subset Complex.ofReal_zero (d.beta j)).trans
        ((d.support j).trans (fun _ hx => hx.1))) member
    have equal : x' = x := chartJ.injOn source' source same
    rw [← equal, oneτ j x' (tsupport_comp_subset Complex.ofReal_zero (d.beta j) member),
      Complex.ofReal_one]
  have costNonneg (y : Y) (labels : Fin (N+1) → tubes) (j' : tubes) :
      0 ≤ domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
        (fun x => |τ j' (FiniteJetComposition.word maps N x)| *
          nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x * g x) maps N
            labels x) := by
    apply Real.sSup_nonneg
    rintro a (zero | ⟨x, _, rfl⟩)
    · rw [mem_singleton_iff.mp zero]
    · apply mul_nonneg (abs_nonneg _)
      unfold nativeWordCost
      exact div_nonneg (mul_nonneg (FiniteSmoothCapturePartition.wordCutoff_nonneg d _ _)
        (abs_nonneg _)) (LinearMap.normDet_nonneg _)
  have costLe : ∑ y : Y, ∑ ℓ : Fin N → tubes, pieceCost y ℓ ≤ cost := by
    apply Finset.sum_le_sum
    intro y _
    calc ∑ ℓ : Fin N → tubes, pieceCost y ℓ
        = ∑ labels ∈ (Finset.univ : Finset (Fin N → tubes)).image (Fin.cons i),
            domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
              (fun x => |τ j (FiniteJetComposition.word maps N x)| *
                nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x * g x) maps N
                  labels x) := by
          have injective : Set.InjOn (fun ℓ : Fin N → tubes => (Fin.cons i ℓ : Fin (N+1) → tubes))
              (Finset.univ : Finset (Fin N → tubes)) := by
            intro a _ b _ h
            exact Fin.cons_right_injective (α := fun _ : Fin (N+1) => tubes) i h
          rw [Finset.sum_image injective]
      _ ≤ ∑ labels : Fin (N+1) → tubes,
            domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
              (fun x => |τ j (FiniteJetComposition.word maps N x)| *
                nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x * g x) maps N
                  labels x) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun labels _ _ => costNonneg y labels j)
      _ ≤ ∑ labels : Fin (N+1) → tubes, ∑ j' : tubes,
            domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
              (fun x => |τ j' (FiniteJetComposition.word maps N x)| *
                nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x * g x) maps N
                  labels x) := by
          apply Finset.sum_le_sum
          intro labels _
          exact Finset.single_le_sum (f := fun j' : tubes =>
            domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
              (fun x => |τ j' (FiniteJetComposition.word maps N x)| *
                nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x * g x) maps N
                  labels x)) (fun j' _ => costNonneg y labels j') (Finset.mem_univ j)
  have nonnegativeK : 0 ≤ K := by
    apply mul_nonneg (mul_nonneg (le_max_of_le_left (by positivity))
      (BTLinkedDyadicWeights.rowConstant_positive t s ht hs).le)
    exact le_max_of_le_left (Real.rpow_nonneg (by positivity) _)
  have piece : ∀ (y : Y) (ℓ : Fin N → tubes),
      ∃ out : EuclideanSmoothHolderCore.space (polarizedTubeLocalSupport_compact atlas d i).closure hb₀ hb₀1,
        (∀ z, EuclideanSmoothHolderCore.physical (polarizedTubeLocalSupport_compact atlas d i).closure hb₀ hb₀1
          out z = ChartLocalization.coordinate chartI (pieceCutoff y ℓ) pieceAmplitude z * input z) ∧
        ‖CompactHolderPhysicalBlocks.realize (volume : Measure (EuclideanSpace ℝ ιleaf))
          (GraphJacobian.densityBound_nonneg (ι := ιleaf) (Heterogeneous.commonSlope planes plus cone))
          (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis o) outputRadial
          outputAngle (polarizedTubeLocalSupport_compact atlas d i) hb₀ hb₀1 (exponent t s) margin out‖ ≤
        ((A : ℝ) * K * pieceCost y ℓ) * strong + weakCoefficient j * weak := by
    intro y ℓ
    let labelsFull : Fin (N+1) → tubes := Fin.cons i ℓ
    let ref : Fin (N+1) → tubes := fun k => if k = Fin.last N then j else labelsFull k
    let θ' := fun m => pieceCutoff y ℓ m * (τ j (points m N) : ℂ)
    let amp' := fun m => (killed m : ℂ)
    have pieceEq (m : M) : pieceCutoff y ℓ m * pieceAmplitude m = θ' m * amp' m := by
      simp only [pieceAmplitude, θ', amp', native]
      ring
    have coordinateEq (z : system.EuclideanModel) :
        ChartLocalization.coordinate chartI (pieceCutoff y ℓ) pieceAmplitude z =
          ChartLocalization.coordinate chartI θ' amp' z := by
      by_cases target : z ∈ chartI.target
      · simp only [ChartLocalization.coordinate, ite_eq_left target]
        exact pieceEq _
      · simp only [ChartLocalization.coordinate, ite_eq_right target]
    have costPieceNonneg : 0 ≤ pieceCost y ℓ := costNonneg y labelsFull j
    by_cases zero : ∀ m, θ' m * amp' m = 0
    · refine ⟨0, ?_, ?_⟩
      · intro z
        rw [_root_.map_zero, coordinateEq]
        by_cases target : z ∈ chartI.target
        · simp only [ChartLocalization.coordinate, ite_eq_left target, zero, zero_mul]
          rfl
        · simp only [ChartLocalization.coordinate, ite_eq_right target, zero_mul]
          rfl
      · rw [_root_.map_zero, norm_zero]
        exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg A.coe_nonneg nonnegativeK)
          costPieceNonneg) (norm_nonneg _)) (mul_nonneg (nonnegativeWeak j) (norm_nonneg _))
    have exists₀ : ∃ m, θ' m * amp' m ≠ 0 := by
      by_contra none
      exact zero (fun m => by
        by_contra hm
        exact none ⟨m, hm⟩)
    obtain ⟨m₀, nonzero₀⟩ := exists₀
    have refZero : ref 0 = i := by
      have : (0 : Fin (N+1)) ≠ Fin.last N := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_zero, Fin.val_last] at this
        omega
      simp only [ref, this, ite_false, labelsFull, Fin.cons_zero]
    have refLast : ref (Fin.last N) = j := by simp only [ref, ite_true]
    have refBefore (k : Fin (N+1)) (hk : k ≠ Fin.last N) : ref k = labelsFull k := by
      simp only [ref, hk, ite_false]
    have continuousCutoffWord : Continuous (fun m => FiniteSmoothCapturePartition.wordCutoff d
        (fun k : Fin (N+1) => points m k.val) labelsFull) :=
      FiniteSmoothCapturePartition.wordCutoff_continuous d
        (fun k m => points m k.val) (fun k => continuousPoints k.val) labelsFull
    have continuousθ' : Continuous θ' :=
      ((Complex.continuous_ofReal.comp (p.smooth y).continuous).mul
        (Complex.continuous_ofReal.comp continuousCutoffWord)).mul
        (Complex.continuous_ofReal.comp ((smoothτ j).continuous.comp (continuousPoints N)))
    have continuousKilled : Continuous killed := by
      apply continuous_finsetProd
      intro k _
      exact (continuousχ.comp (continuousPoints k)).mul (continuousg.comp (continuousPoints k))
    have continuousAmp' : Continuous amp' := Complex.continuous_ofReal.comp continuousKilled
    have supportθ' : tsupport θ' ⊆ ⋂ k : Fin (N+1),
        (fun m => CylinderPrincipalCoefficient.prefixOrbit
          (fun k : Fin N => F.family ε (control k).val) (fun k => k) k.val m) ⁻¹'
            atlas.normalizedTube radiusT (ref k).val := by
      intro m hm
      have cylinder := FiniteSmoothCapturePartition.wordCutoff_tsupport_subset d
        (fun k m => points m k.val) (fun k => continuousPoints k.val) labelsFull
      have pressureWord := tsupport_mul_subset_left
        (f := fun m => pieceCutoff y ℓ m) (g := fun m => (τ j (points m N) : ℂ)) hm
      have wordMember := tsupport_mul_subset_right
        (f := fun m => (p.beta y m : ℂ))
        (g := fun m => (FiniteSmoothCapturePartition.wordCutoff d
          (fun k : Fin (N+1) => points m k.val) labelsFull : ℂ)) pressureWord
      have realWord := tsupport_comp_subset Complex.ofReal_zero
        (fun m => FiniteSmoothCapturePartition.wordCutoff d
          (fun k : Fin (N+1) => points m k.val) labelsFull) wordMember
      have cylinderMember := cylinder realWord
      have terminalTerm := tsupport_mul_subset_right
        (f := fun m => pieceCutoff y ℓ m) (g := fun m => (τ j (points m N) : ℂ)) hm
      have terminalReal := tsupport_comp_subset Complex.ofReal_zero
        (fun m => τ j (points m N)) terminalTerm
      have terminalMember : points m N ∈ tsupport (τ j) :=
        tsupport_comp_subset_preimage (τ j) (continuousPoints N) terminalReal
      apply mem_iInter.mpr
      intro k
      change CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) k.val m ∈
          atlas.normalizedTube radiusT (ref k).val
      rw [show CylinderPrincipalCoefficient.prefixOrbit
          (fun k : Fin N => F.family ε (control k).val) (fun k => k) k.val m = points m k.val from
        (prefixOrbit_reindex (fun c : cube (ι := ι) ε => F.family ε c.val) control k.val m).symm]
      by_cases hk : k = Fin.last N
      · subst hk
        rw [refLast]
        exact supportτ j terminalMember
      · rw [refBefore k hk]
        exact mem_iInter.mp cylinderMember k
    have trackedA : ∀ k : Fin (N+1), CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) k.val m₀ ∈
          atlas.normalizedTube radiusA (ref k).val := by
      intro k
      have member := mem_iInter.mp (supportθ' (subset_tsupport θ' (left_ne_zero_of_mul nonzero₀))) k
      exact ⟨member.1, ball_subset_ball smallT member.2⟩
    have admissibleRef : adaptedTubeWordAdmissible atlas η tubes ref := by
      intro k
      exact admissibility ε hp hwAdm N control (fun k => (ref k).val) m₀ trackedA k
    have word := rows j ε hp hwPiece control ref admissibleRef
    obtain ⟨H, agreement, native', identity', smooth', inverseSmooth', bound⟩ := word
    have identityCube : (native' : M → M) = native := by
      funext m
      rw [identity']
      exact (prefixOrbit_reindex (fun c : cube (ι := ι) ε => F.family ε c.val) control N m).symm
    have holderPiece := holder ε hp hwHolder N control labelsFull y j
    obtain ⟨gH, formulaH, normH, supportH, holderH⟩ := holderPiece
    have agreementPiece := F.adapted_tubeWord_output_agreement atlas (radius := radiusT)
      (agreementRadius := tubeCap) (smallT.trans belowRadiusA) tubes ε hp hwWindow control ref
      θ' amp' continuousθ' continuousAmp' supportθ' H agreement native' identity'
    obtain ⟨O, supportO, insideO, equalO⟩ := agreementPiece
    have chart0 : AdaptedTubeWord.chart atlas tubes ref 0 = chartI := by
      have := AdaptedTubeWord.chart_eq atlas tubes ref (0 : Fin (N+1))
      rw [refZero] at this
      exact this
    have chartN : AdaptedTubeWord.chart atlas tubes ref N = chartJ := by
      have := AdaptedTubeWord.chart_eq atlas tubes ref (Fin.last N)
      rw [refLast, Fin.val_last] at this
      exact this
    rw [chart0] at supportO insideO equalO
    rw [chartN] at insideO equalO
    have productEq (m : M) : (p.beta y m : ℂ) *
        (FiniteSmoothCapturePartition.wordCutoff d (fun k : Fin (N+1) =>
          CylinderPrincipalCoefficient.prefixOrbit (fun c : cube (ι := ι) ε => F.family ε c.val)
            control k.val m) labelsFull : ℂ) *
        (ActualFiniteRegularWord.weight (fun c : cube (ι := ι) ε => F.family ε c.val)
          (fun x => χ x * g x) (List.ofFn control) m *
          (τ j (CylinderPrincipalCoefficient.prefixOrbit
            (fun c : cube (ι := ι) ε => F.family ε c.val) control N m) : ℂ)) = θ' m * amp' m := by
      rw [weight_ofFn_eq_range]
      simp only [θ', amp', pieceCutoff, killed, points]
      ring
    have coordinateFunction : (fun z => ChartLocalization.coordinate chartI
        (fun m => (p.beta y m : ℂ) *
          (FiniteSmoothCapturePartition.wordCutoff d (fun k : Fin (N+1) =>
            CylinderPrincipalCoefficient.prefixOrbit (fun c : cube (ι := ι) ε => F.family ε c.val)
              control k.val m) labelsFull : ℂ))
        (fun m => ActualFiniteRegularWord.weight (fun c : cube (ι := ι) ε => F.family ε c.val)
          (fun x => χ x * g x) (List.ofFn control) m *
          (τ j (CylinderPrincipalCoefficient.prefixOrbit
            (fun c : cube (ι := ι) ε => F.family ε c.val) control N m) : ℂ)) z) =
        ChartLocalization.coordinate chartI θ' amp' := by
      funext z
      by_cases target : z ∈ chartI.target
      · simp only [ChartLocalization.coordinate, ite_eq_left target]
        rw [← productEq]
      · simp only [ChartLocalization.coordinate, ite_eq_right target]
    have holderFormula (z : system.EuclideanModel) :
        gH z = ChartLocalization.coordinate chartI θ' amp' z := by
      rw [formulaH z]
      exact congrFun coordinateFunction z
    have compactU : HasCompactSupport (u.val : system.EuclideanModel → ℂ) :=
      HasCompactSupport.intro (polarizedTubeLocalSupport_compact atlas d j) (fun x hx => u.property x hx)
    have betaSourceJ : tsupport (fun m => (d.beta j m : ℂ)) ⊆ chartJ.source :=
      (tsupport_comp_subset Complex.ofReal_zero (d.beta j)).trans
        ((d.support j).trans (fun _ hx => hx.1))
    have supportU : tsupport (u.val : system.EuclideanModel → ℂ) ⊆ chartJ.target := by
      have inside : tsupport (u.val : system.EuclideanModel → ℂ) ⊆
          ChartLocalization.localSupport chartJ (fun m => (d.beta j m : ℂ)) := by
        apply closure_minimal _ (polarizedTubeLocalSupport_compact atlas d j).isClosed
        intro x hx
        by_contra outside
        exact hx (u.property x outside)
      refine inside.trans ?_
      rintro _ ⟨x, hx, rfl⟩
      exact chartJ.map_source (betaSourceJ hx)
    let Wword := prefixHomeomorph H (fun k : Fin N => k) N
    have supportCoordinate : tsupport (fun z => ChartLocalization.coordinate chartI
        (fun m => (p.beta y m : ℂ) *
          (FiniteSmoothCapturePartition.wordCutoff d (fun k : Fin (N+1) =>
            CylinderPrincipalCoefficient.prefixOrbit (fun c : cube (ι := ι) ε => F.family ε c.val)
              control k.val m) labelsFull : ℂ))
        (fun m => ActualFiniteRegularWord.weight (fun c : cube (ι := ι) ε => F.family ε c.val)
          (fun x => χ x * g x) (List.ofFn control) m *
          (τ j (CylinderPrincipalCoefficient.prefixOrbit
            (fun c : cube (ι := ι) ε => F.family ε c.val) control N m) : ℂ)) z) ⊆ O := by
      rw [coordinateFunction]
      exact supportO
    have outputPiece := F.adapted_tube_source_terminal_physical_output μE regularity atlas d hb₀ hb₀1
      hb₀q regularKilled ε hp hwWindow control labelsFull (fun m => (p.beta y m : ℂ))
      (smoothPressureC y) j (fun m => (τ j m : ℂ)) (smoothτC j) u.val compactU supportU native'
      identityCube Wword O supportCoordinate insideO equalO
    obtain ⟨out, represented⟩ := outputPiece
    have represented' (z : system.EuclideanModel) :
        EuclideanSmoothHolderCore.physical (polarizedTubeLocalSupport_compact atlas d i).closure hb₀ hb₀1 out z =
          gH z * u.val (Wword z) := by
      rw [formulaH z]
      exact represented z
    let extension := fun n : ℕ => if h : n < N then control ⟨n, h⟩ else control ⟨0, positiveN⟩
    have wordAgree : ∀ k ≤ N, ∀ m, points m k = FiniteJetComposition.word maps k m := by
      intro k hk m
      exact prefixOrbit_eq_jetWord (fun c : cube (ι := ι) ε => F.family ε c.val) control extension
        (fun n h => by simp only [extension, dite_eq_left h]) k hk m
    have identityWord : (native' : M → M) = FiniteJetComposition.word maps N := by
      funext m
      rw [identityCube]
      exact wordAgree N le_rfl m
    have costLemma := piece_native_cost_bound b.hyperbolic.normedAdaptedProjection d p y χ g (τ j)
      continuousχ continuousg (smoothτ j).continuous W supportχ collar maps
      (fun n => continuousMaps _) positiveN labelsFull native' identityWord smooth'
      (inverseSmooth'.mdifferentiable one_ne_zero)
    have costBound : ∀ m, ‖θ' m * amp' m‖ₑ ≤ ((pieceCost y ℓ).toNNReal : ℝ≥0∞) *
        ENNReal.ofReal (((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) native' m).toLinearMap.domRestrict
          (b.hyperbolic.normedAdaptedProjection.unstable m)).normDet) := by
      intro m
      have pointsWord : (fun k : Fin (N+1) => points m k.val) =
          (fun k : Fin (N+1) => FiniteJetComposition.word maps k.val m) :=
        funext fun k => wordAgree k.val (Nat.le_of_lt_succ k.isLt) m
      have productWord : killed m = ∏ k ∈ Finset.range N,
          χ (FiniteJetComposition.word maps k m) * g (FiniteJetComposition.word maps k m) :=
        Finset.prod_congr rfl fun k hk => by
          rw [wordAgree k (Finset.mem_range.mp hk).le m]
      have nativeValue : native' m = points m N := congrFun identityCube m
      have lhs : θ' m * amp' m = (p.beta y m : ℂ) *
          (FiniteSmoothCapturePartition.wordCutoff d
            (fun k : Fin (N+1) => FiniteJetComposition.word maps k.val m) labelsFull : ℂ) *
          (((∏ k ∈ Finset.range N, χ (FiniteJetComposition.word maps k m) *
            g (FiniteJetComposition.word maps k m)) : ℝ) : ℂ) * (τ j (native' m) : ℂ) := by
        rw [← productWord, ← pointsWord, nativeValue]
        simp only [θ', amp', pieceCutoff]
        ring
      rw [lhs]
      exact costLemma m
    have formulaRef (z : system.EuclideanModel) : gH z =
        ChartLocalization.coordinate (AdaptedTubeWord.chart atlas tubes ref 0) θ' amp' z := by
      rw [chart0]
      exact holderFormula z
    have supportG : tsupport (fun w => gH w) ⊆ tubeAmplitudeSupport atlas d :=
      supportH.trans (localSupport_subset_tubeAmplitudeSupport atlas d (labelsFull 0))
    have rowBound := bound θ' amp' continuousθ' continuousAmp' supportθ' gH formulaRef supportG
      (fun w => (gH.norm_coe_le_norm w).trans normH) holderH (pieceCost y ℓ).toNNReal costBound u
      (polarizedTubeLocalSupport_compact atlas d i) out represented'
    have coeCost : ((A * (pieceCost y ℓ).toNNReal : ℝ≥0) : ℝ) = (A : ℝ) * pieceCost y ℓ := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ costPieceNonneg]
    have pieceLe : pieceCost y ℓ ≤ costCap := by
      have inner : pieceCost y ℓ ≤ ∑ ℓ' : Fin N → tubes, pieceCost y ℓ' :=
        Finset.single_le_sum (f := fun ℓ' => pieceCost y ℓ')
          (fun ℓ' _ => costNonneg y (Fin.cons i ℓ') j) (Finset.mem_univ ℓ)
      have outer : ∑ ℓ' : Fin N → tubes, pieceCost y ℓ' ≤
          ∑ y' : Y, ∑ ℓ' : Fin N → tubes, pieceCost y' ℓ' :=
        Finset.single_le_sum (f := fun y' => ∑ ℓ' : Fin N → tubes, pieceCost y' ℓ')
          (fun y' _ => Finset.sum_nonneg fun ℓ' _ => costNonneg y' (Fin.cons i ℓ') j)
          (Finset.mem_univ y)
      exact ((inner.trans outer).trans costLe).trans hcost
    refine ⟨out, ?_, ?_⟩
    · intro z
      rw [represented' z, holderFormula z, ← coordinateEq z]
      by_cases vanish : ChartLocalization.coordinate chartI (pieceCutoff y ℓ) pieceAmplitude z = 0
      · rw [vanish, zero_mul, zero_mul]
      · congr 1
        have member : z ∈ O :=
          supportO (subset_tsupport _ (fun h => vanish ((coordinateEq z).trans h)))
        have source := (ChartedHomeomorphCoordinateMap.coordinateMap_source chartI chartJ native' z).mp
          (insideO member)
        have value : Wword z = chartJ (native' (chartI.symm z)) := equalO member
        have nativeEq : native' (chartI.symm z) = native (chartI.symm z) := congrFun identityCube _
        rw [nativeEq] at value source
        have inputValue : input z = u.val (chartJ (native (chartI.symm z))) := ite_eq_left source.2
        rw [value, inputValue]
    · have key : ∀ a c : ℝ, 0 ≤ c →
          ((A * (pieceCost y ℓ).toNNReal : ℝ≥0) : ℝ) *
              ((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*
                max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s)) * a +
            ((rem j : ℝ)*(2*(1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹) +
              ((A * (pieceCost y ℓ).toNNReal : ℝ≥0) : ℝ)*(2*(((frequencyCutoff j+1:ℕ):ℝ)*
                (2:ℝ)^((t-s+loss)*(((frequencyCutoff j+1:ℕ):ℝ)))))) * c ≤
          ((A : ℝ) * K * pieceCost y ℓ) * a + weakCoefficient j * c := by
        intro a c hc
        rw [coeCost]
        apply add_le_add (le_of_eq (by ring))
        apply mul_le_mul_of_nonneg_right _ hc
        show _ ≤ (rem j : ℝ) * (2 * (1 - (2:ℝ) ^ (-(α - (t - s + loss))))⁻¹) +
          ((A : ℝ) * costCap) * (2 * (((frequencyCutoff j + 1 : ℕ) : ℝ) *
            (2:ℝ) ^ ((t - s + loss) * (((frequencyCutoff j + 1 : ℕ) : ℝ)))))
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pieceLe A.coe_nonneg)
        positivity
      exact rowBound.trans (key _ _ (norm_nonneg _))
  choose out outPhysical outBound using piece
  refine ⟨∑ y : Y, ∑ ℓ : Fin N → tubes, out y ℓ, ?_, ?_⟩
  · intro z
    have captureFin : ∀ m, d.beta i m * killed m ≠ 0 →
        m ∈ p.capture ∧ ∀ k : Fin N, (fun m (k : Fin (N+1)) => points m k.val) m k.succ ∈ d.capture := by
      intro m hm
      refine ⟨(capture i m hm).1, fun k => ?_⟩
      have member := (capture i m hm).2 k
      simpa only [Fin.val_succ] using member
    have decomposition := chart_pair_piece_decomposition (Y := Y) d p chartI chartJ i
      (fun m (k : Fin (N+1)) => points m k.val) (fun m => rfl) native killed
      (fun x => (τ j x : ℂ)) u.val terminal captureFin z
    rw [decomposition]
    simp only [map_sum, BoundedContinuousFunction.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun ℓ _ => outPhysical y ℓ z
  · let R := fun (y : Y) (ℓ : Fin N → tubes) => CompactHolderPhysicalBlocks.realize
      (volume : Measure (EuclideanSpace ℝ ιleaf))
      (GraphJacobian.densityBound_nonneg (ι := ιleaf) (Heterogeneous.commonSlope planes plus cone))
      (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis o) outputRadial
      outputAngle (polarizedTubeLocalSupport_compact atlas d i) hb₀ hb₀1 (exponent t s) margin (out y ℓ)
    have linear : CompactHolderPhysicalBlocks.realize (volume : Measure (EuclideanSpace ℝ ιleaf))
        (GraphJacobian.densityBound_nonneg (ι := ιleaf) (Heterogeneous.commonSlope planes plus cone))
        (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis o) outputRadial
        outputAngle (polarizedTubeLocalSupport_compact atlas d i) hb₀ hb₀1 (exponent t s) margin
        (∑ y : Y, ∑ ℓ : Fin N → tubes, out y ℓ) = ∑ y : Y, ∑ ℓ : Fin N → tubes, R y ℓ := by
      simp only [R, map_sum]
    refine (congrArg norm linear).trans_le ?_
    calc ‖∑ y : Y, ∑ ℓ : Fin N → tubes, R y ℓ‖ ≤ ∑ y : Y, ∑ ℓ : Fin N → tubes, ‖R y ℓ‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => norm_sum_le _ _)
      _ ≤ ∑ y : Y, ∑ ℓ : Fin N → tubes,
            (((A : ℝ) * K * pieceCost y ℓ) * strong + weakCoefficient j * weak) := by
          exact Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun ℓ _ => outBound y ℓ
      _ = ((A : ℝ) * K * ∑ y : Y, ∑ ℓ : Fin N → tubes, pieceCost y ℓ) * strong +
            (∑ _y : Y, ∑ _ℓ : Fin N → tubes, weakCoefficient j) * weak := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := by
          have principal : (A : ℝ) * K * (∑ y : Y, ∑ ℓ : Fin N → tubes, pieceCost y ℓ) ≤
              (A : ℝ) * K * cost :=
            mul_le_mul_of_nonneg_left costLe (mul_nonneg A.coe_nonneg nonnegativeK)
          exact add_le_add (mul_le_mul_of_nonneg_right principal (norm_nonneg _)) le_rfl

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
