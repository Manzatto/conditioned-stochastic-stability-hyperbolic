module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedPolarizedChartPairTwoNorm
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierBounds
meta import Lean.LibrarySuggestions.Basic

/-! The rows produced by the polarized chart-pair bound, with the shared
unit fake-leaf data, are literally carrier rows. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "rows_of_producer"
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "adapted_polarized_carrier_rows"

public noncomputable section
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AllFakeLeafModel AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open AdaptedTubeUnitCarrierBounds

variable {E M ι : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem rows_of_producer (atlas : ChartAtlas system) {radius : ℝ}
    {tubes : Finset atlas.NormalizedTubeIndex}
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : tubes => atlas.normalizedTube radius i.val))
    {b₀ : ℝ} (hb₀ : 0 < b₀) (hb₀1 : b₀ < 1)
    (positiveStable : 0 < system.framing.stableDimension)
    (radial : ConeDyadicSymbols.RadialCutoff)
    (angle : ConeDyadicSymbols.AngularCutoff
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (ProjectionConeTransversality.cone system.euclideanSecondProjection
        (OneStepConePolarization.minusOpening system.rate)))
    (exponent : Bool → ℝ) (margin : ∀ a, exponent a ≤ b₀) {loss : ℝ} (positiveLoss : 0 < loss)
    (Fw : M → M) (gw : M → ℝ) (strong : ℝ) (remainder : tubes → tubes → ℝ)
    (produced : ∀ i j : tubes,
      ∀ u : SchwartzJetSpace.supportedCore (ChartLocalization.localSupport
        (atlas.normalizedTubeChart j.val) (fun m => (d.beta j m : ℂ))),
      ∃ output : EuclideanSmoothHolderCore.space (polarizedTubeLocalSupport_compact atlas d i).closure hb₀ hb₀1,
        (∀ z, EuclideanSmoothHolderCore.physical (polarizedTubeLocalSupport_compact atlas d i).closure hb₀ hb₀1
          output z = ChartPairTransfer.pair (atlas.normalizedTubeChart i.val)
            (atlas.normalizedTubeChart j.val) (fun m => (d.beta i m : ℂ)) Fw gw u.val z) ∧
        ‖CompactHolderPhysicalBlocks.realize
          (volume : Measure (EuclideanSpace ℝ (Fin system.framing.unstableDimension)))
          (GraphJacobian.densityBound_nonneg (ι := Fin system.framing.unstableDimension)
            (Heterogeneous.commonSlope (unitPlanes system) (unitPlus system)
              (unitCone system positiveStable)))
          (AllFakeLeafHolderCoreBounds.leaves (unitPlanes system) (unitPlus system)
            (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) ())
          radial angle (polarizedTubeLocalSupport_compact atlas d i) hb₀ hb₀1 exponent margin output‖ ≤
        strong *
          ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
            (unitCone system positiveStable) (unitCoordinates system) (unitBasis system)
            radial angle (polarizedTubeLocalSupport_compact atlas d j) hb₀ hb₀1
            exponent margin () u‖ +
        remainder i j *
          ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
            (unitCone system positiveStable) (unitCoordinates system) (unitBasis system)
            radial angle (polarizedTubeLocalSupport_compact atlas d j) hb₀ hb₀1
            (fun sign => exponent sign - loss)
            (fun sign => (sub_le_self _ positiveLoss.le).trans (margin sign)) () u‖) :
    Rows atlas d hb₀ hb₀1 positiveStable radial angle exponent margin positiveLoss Fw gw strong
      remainder :=
  produced

set_option maxHeartbeats 3200000 in
/-- The polarized chart-pair producer with the shared unit fake-leaf data and
one cutoff family on both sides, whose output is directly carrier rows. The
producer's cost and capture lets are explicit hypotheses. -/
theorem Maps.adapted_polarized_carrier_rows {r α q : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (αq : α < q)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (atlas : ChartAtlas system) (positiveStable : 0 < system.framing.stableDimension)
    (radial : ConeDyadicSymbols.RadialCutoff)
    (cutoffs : ConstructedEnlargedConeSymbols.Cutoffs
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (ProjectionConeTransversality.cone system.euclideanSecondProjection
        (OneStepConePolarization.minusOpening system.rate))) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∃ ν : ℝ, 1 < ν ∧ ∃ A : NNReal,
    ∃ tubeCap : ℝ, 0 < tubeCap ∧ ∃ cutoff : NNReal, 0 < cutoff ∧ cutoff ≤ F.window ∧
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
      ∃ window : NNReal, 0 < window ∧ window ≤ cutoff ∧
      ∀ N : ℕ, ∀ positiveN : 0 < N,
      ∀ {b₀ : ℝ} (hb₀ : 0 < b₀) (hb₀1 : b₀ < 1), b₀ < q →
      ∀ (t s loss : ℝ), 0 < t → s < 0 → ∀ positiveLoss : 0 < loss, t-s+loss < α →
      ∀ margin : (∀ sign, BTLinkedDyadicWeights.exponent t s sign ≤ b₀),
      ∀ costCap : ℝ, 0 ≤ costCap →
      ∃ remainder : tubes → tubes → ℝ, (∀ i j, 0 ≤ remainder i j) ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ window →
      ∀ control : Fin N → cube (ι := ι) ε,
      (∑ y : Y, ∑ labels : Fin (N+1) → tubes, ∑ j : tubes,
        PressureCoverRefinement.domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
          (fun x => |τ j (FiniteJetComposition.word
              (fun n : ℕ => F.family ε
                (if h : n < N then control ⟨n, h⟩ else control ⟨0, positiveN⟩).val) N x)| *
            nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x * g x)
              (fun n : ℕ => F.family ε
                (if h : n < N then control ⟨n, h⟩ else control ⟨0, positiveN⟩).val)
              N labels x)) ≤ costCap →
      (∀ (i : tubes) (m : M),
        d.beta i m * (∏ k ∈ Finset.range N,
          χ (CylinderPrincipalCoefficient.prefixOrbit
            (fun c : cube (ι := ι) ε => F.family ε c.val) control k m) *
          g (CylinderPrincipalCoefficient.prefixOrbit
            (fun c : cube (ι := ι) ε => F.family ε c.val) control k m)) ≠ 0 →
        m ∈ p.capture ∧ ∀ k : Fin N, CylinderPrincipalCoefficient.prefixOrbit
          (fun c : cube (ι := ι) ε => F.family ε c.val) control (k.val + 1) m ∈ d.capture) →
      Rows atlas d hb₀ hb₀1 positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin positiveLoss
        (CylinderPrincipalCoefficient.prefixOrbit
          (fun c : cube (ι := ι) ε => F.family ε c.val) control N)
        (fun m => ∏ k ∈ Finset.range N,
          χ (CylinderPrincipalCoefficient.prefixOrbit
            (fun c : cube (ι := ι) ε => F.family ε c.val) control k m) *
          g (CylinderPrincipalCoefficient.prefixOrbit
            (fun c : cube (ι := ι) ε => F.family ε c.val) control k m))
        (((A : ℝ) * ((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s)) *
            BTLinkedDyadicWeights.rowConstant t s) *
            max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s))) *
          (∑ y : Y, ∑ labels : Fin (N+1) → tubes, ∑ j : tubes,
            PressureCoverRefinement.domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
              (fun x => |τ j (FiniteJetComposition.word
                  (fun n : ℕ => F.family ε
                    (if h : n < N then control ⟨n, h⟩ else control ⟨0, positiveN⟩).val) N x)| *
                nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x * g x)
                  (fun n : ℕ => F.family ε
                    (if h : n < N then control ⟨n, h⟩ else control ⟨0, positiveN⟩).val)
                  N labels x)))
        remainder := by
  classical
  have h6 := Maps.adapted_polarized_chart_pair_two_norm.{0, 0, 0, _, _, _}
    (Measure.addHaar : Measure E) F positiveα subunitα lower αq regularT backward atlas
    positiveStable radial cutoffs.original
  let μ := h6.choose
  have hμ := h6.choose_spec
  let ν := hμ.2.2.choose
  have hν := hμ.2.2.choose_spec
  let A := hν.2.choose
  have hA := hν.2.choose_spec
  let tubeCap := hA.choose
  have hTube := hA.choose_spec
  let cutoff := hTube.2.choose
  have hCut := hTube.2.choose_spec
  refine ⟨μ, hμ.1, hμ.2.1, ν, hν.1, A, tubeCap, hTube.1, cutoff, hCut.1, hCut.2.1, ?_⟩
  intro radiusT small tubes d Y _ Kp vp p χ g hχ hg hχg W hW hWc τ hτ1 hτ2 hτ3
  have h6' := hCut.2.2 radiusT small tubes d p χ g hχ hg hχg W hW hWc τ hτ1 hτ2 hτ3
  refine ⟨h6'.choose, h6'.choose_spec.1, h6'.choose_spec.2.1, ?_⟩
  intro N positiveN b₀ hb₀ hb₀1 b₀q t s loss ht hs positiveLoss gap margin costCap hcap
  have h := h6'.choose_spec.2.2 N positiveN
    (EuclideanSpace.basisFun (Fin (system.framing.unstableDimension +
      system.framing.stableDimension)) ℝ)
    (unitPlanes system) (unitPlus system) (unitCone system positiveStable)
    (unitCoordinates system) (unitBasis system) () rfl rfl radial cutoffs
    hb₀ hb₀1 b₀q t s loss ht hs positiveLoss.le gap margin costCap hcap
  refine ⟨h.choose, h.choose_spec.1, ?_⟩
  intro ε hε hl control hcost hcapture
  exact rows_of_producer atlas d hb₀ hb₀1 positiveStable radial cutoffs.original _ margin
    positiveLoss _ _ _ _ (h.choose_spec.2 ε hε hl control hcost hcapture)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
