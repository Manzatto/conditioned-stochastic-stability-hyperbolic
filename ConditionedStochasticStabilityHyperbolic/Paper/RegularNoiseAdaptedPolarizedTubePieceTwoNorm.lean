module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedPolarizedNativeTwoNormRows
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeTrackedSupport

/-! The native two-norm bound for one localized piece along an admissible
adapted tube reference word. The producer's reference sequences, their
admissibility, and all four principal-row support conditions are derived
here from the tube word; the caller supplies only facts about the concrete
amplitude (continuity, cylinder support, bounded C^α realization, native
unstable-Jacobian cost) and the represented closed output. The final
reference chart may be the chart of an independent terminal input slot. -/
public noncomputable section
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal SchwartzMap BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
open LeanShared.OrthogonalRateGlobalWordFakeLeaves
open LeanShared.OrthogonalProductCoordinates
open AllFakeLeafModel BTLinkedDyadicWeights

universe uZ uL uK

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

set_option maxHeartbeats 3200000 in
theorem Maps.adapted_polarized_tube_piece_two_norm {r α : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (atlas : ChartAtlas system) (positiveStable : 0 < system.framing.stableDimension)
    (outputRadial : ConeDyadicSymbols.RadialCutoff)
    (outputAngle : ConeDyadicSymbols.AngularCutoff
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (ProjectionConeTransversality.cone system.euclideanSecondProjection
        (OneStepConePolarization.minusOpening system.rate))) :
    let : CompactSpace M := F.atlas.compactSpace;
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∃ ν : ℝ, 1 < ν ∧ ∃ A : ℝ≥0,
    ∃ tubeCap : ℝ, 0 < tubeCap ∧ ∃ η : ℝ, 0 < η ∧
    ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∀ radiusT : ℝ, radiusT ≤ tubeCap → ∀ tubes : Finset atlas.NormalizedTubeIndex,
      ∀ N : ℕ, 0 < N →
      ∀ {Z : Type uZ} {ιleaf : Type uL} {κfreq : Type uK}, ∀ [Finite Z], ∀ [Fintype ιleaf], ∀ [DecidableEq ιleaf], ∀ [Fintype κfreq],
      ∀ (_ambientBasis : OrthonormalBasis κfreq ℝ system.EuclideanModel)
      (planes : Z → Submodule ℝ system.EuclideanModel) (plus : Z → Set system.EuclideanModel)
      (cone : ∀ i, AllFakeLeafModel.ConeData (planes i) (plus i))
      (coordinates : ∀ i, EuclideanSpace ℝ ιleaf ≃ₗᵢ[ℝ] planes i)
      (basis : ∀ i, OrthonormalBasis ιleaf ℝ (planes i)) (i : Z),
      planes i = firstPlane system.euclideanDimension →
      plus i = ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2) →
      ∀ {inputMinus : Set system.EuclideanModel} (inputRadial : ConeDyadicSymbols.RadialCutoff)
      (inputCutoffs : ConstructedEnlargedConeSymbols.Cutoffs (plus i) inputMinus)
      {amplitudeSupport : Set system.EuclideanModel}, IsCompact amplitudeSupport →
      ∀ {G₀ G₁ : ℝ}, 0 ≤ G₀ → 0 ≤ G₁ →
      ∀ {inputSupport : Set system.EuclideanModel} (compactInput : IsCompact inputSupport)
      {b₀ : ℝ} (hb₀ : 0 < b₀) (hb₀1 : b₀ < 1)
      (t s loss : ℝ), 0 < t → s < 0 → ∀ hLoss : 0 ≤ loss, t-s+loss < α →
      ∀ margin : (∀ sign, exponent t s sign ≤ b₀),
      ∃ frequencyCutoff : ℕ, ∃ remainder : ℝ≥0,
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff →
      ∀ control : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N+1) → tubes,
      adaptedTubeWordAdmissible atlas η tubes labels →
      let c := AdaptedTubeWord.center atlas tubes labels
      let p := AdaptedTubeWord.reference atlas tubes labels
      let inside := AdaptedTubeWord.reference_mem atlas tubes labels
      let κ := AdaptedTubeWord.chart atlas tubes labels
      ∃ H : Fin N → system.EuclideanModel ≃ₜ system.EuclideanModel,
      (∀ k : Fin N,
        let L := ContinuousCenteredFrameCharts.chartFrame (c k.val).val (p k.val).val
          (atlas.inside (c k.val) (inside k.val)).2
          (system.euclideanReferenceFrame (c k.val) ⟨p k.val,atlas.inside (c k.val) (inside k.val)⟩)
        let R := ContinuousCenteredFrameCharts.chartFrame (c (k.val+1)).val (p (k.val+1)).val
          (atlas.inside (c (k.val+1)) (inside (k.val+1))).2
          (system.euclideanReferenceFrame (c (k.val+1))
            ⟨p (k.val+1),atlas.inside (c (k.val+1)) (inside (k.val+1))⟩)
        ∀ z ∈ closedBall 0 tubeCap,
          H k z = centered L R ((chartAt E (c k.val).val) (p k.val).val)
            ((chartAt E (c (k.val+1)).val) (p (k.val+1)).val)
            (chartAt E (c (k.val+1)).val ∘ F.family ε (control k).val ∘
              (chartAt E (c k.val).val).symm) z) ∧
      ∃ native : M ≃ₜ M,
        (native : M → M) = CylinderPrincipalCoefficient.prefixOrbit
          (fun k : Fin N => F.family ε (control k).val) (fun k => k) N ∧
        ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 native ∧
        ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 native.symm ∧
      let W := prefixHomeomorph H (fun k : Fin N => k) N
      ∀ θ amplitude : M → ℂ, Continuous θ → Continuous amplitude →
        tsupport θ ⊆ ⋂ j : Fin (N+1),
          (fun m => CylinderPrincipalCoefficient.prefixOrbit
            (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m) ⁻¹'
              atlas.normalizedTube radiusT (labels j).val →
      ∀ g : system.EuclideanModel →ᵇ ℂ,
        (∀ z, g z = ChartLocalization.coordinate (κ 0) θ amplitude z) →
        tsupport (fun w => g w) ⊆ amplitudeSupport →
        (∀ w, ‖g w‖ ≤ G₀) → (∀ z w, ‖g z-g w‖ ≤ G₁*dist z w^α) →
      ∀ cost : ℝ≥0,
        (∀ m : M, ‖θ m * amplitude m‖ₑ ≤ (cost:ℝ≥0∞)*ENNReal.ofReal
          (((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) native m).toLinearMap.domRestrict
            (b.hyperbolic.normedAdaptedProjection.unstable m)).normDet)) →
      ∀ f : SchwartzJetSpace.supportedCore inputSupport,
      ∀ {outputSupport : Set system.EuclideanModel} (compactOutput : IsCompact outputSupport)
        (output : EuclideanSmoothHolderCore.space compactOutput.closure hb₀ hb₀1),
        (∀ z, EuclideanSmoothHolderCore.physical compactOutput.closure hb₀ hb₀1 output z =
          g z * f.val (W z)) →
          ‖CompactHolderPhysicalBlocks.realize (volume : Measure (EuclideanSpace ℝ ιleaf))
            (GraphJacobian.densityBound_nonneg (ι := ιleaf) (Heterogeneous.commonSlope planes plus cone))
            (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis i) outputRadial outputAngle compactOutput hb₀ hb₀1
            (exponent t s) margin output‖ ≤
          ((A * cost : ℝ≥0) : ℝ) *
            ((max ((2:ℝ)^(6*t)) ((2:ℝ)^(-7*s))*rowConstant t s)*
              max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s))*
            ‖AllFakeLeafHolderCoreBounds.coreBlocks planes plus cone coordinates basis
              inputRadial inputCutoffs.original compactInput hb₀ hb₀1 (exponent t s) margin i f‖ +
          ((remainder : ℝ)*(2*(1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹) +
            ((A * cost : ℝ≥0) : ℝ)*(2*(((frequencyCutoff+1:ℕ):ℝ)*
              (2:ℝ)^((t-s+loss)*(((frequencyCutoff+1:ℕ):ℝ))))))*
            ‖AllFakeLeafHolderCoreBounds.coreBlocks planes plus cone coordinates basis
              inputRadial inputCutoffs.original compactInput hb₀ hb₀1
              (fun sign => exponent t s sign-loss)
              (fun sign => (sub_le_self _ hLoss).trans (margin sign)) i f‖ := by
  intro compactM
  have rows := Maps.adapted_polarized_native_two_norm_rows.{uZ, uL, uK, _, _, _} F (b := b) (system := system)
      positiveα subunitα lower regularT backward atlas positiveStable outputRadial outputAngle
  rcases rows with ⟨μ,positiveμ,contractingμ,ν,expandingν,K,positiveK,rowRadius,positiveRowRadius,A,
    radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,C,Cinv,nonnegativeC,nonnegativeCinv,family⟩
  refine ⟨μ,positiveμ,contractingμ,ν,expandingν,A,?_⟩
  refine ⟨min rowRadius (radius/2),lt_min positiveRowRadius (by linarith),η,positiveη,
    cutoff,positiveCutoff,cap,?_⟩
  intro radiusT smallT tubes N large Z ιleaf κfreq _ _ _ _ ambientBasis planes plus cone coordinates basis i
    planeSame plusSame inputMinus inputRadial inputCutoffs amplitudeSupport compactAmplitude G₀ G₁
    nonnegativeG₀ nonnegativeG₁ inputSupport compactInput b₀ hb₀ hb₀1 t s loss ht hs hLoss gap margin
  have rowsAll := family N large ambientBasis planes plus cone
    coordinates basis i planeSame plusSame inputRadial inputCutoffs compactAmplitude nonnegativeG₀
    nonnegativeG₁ compactInput hb₀ hb₀1
  have rowsT := rowsAll t s loss ht hs hLoss gap margin
  obtain ⟨frequencyCutoff,remainder,perWord⟩ := rowsT
  refine ⟨frequencyCutoff,remainder,?_⟩
  intro ε hp hw control labels admissible
  have near := AdaptedTubeWord.reference_admissible atlas tubes labels admissible
  have word := perWord ε hp hw control
    (fun k => AdaptedTubeWord.center atlas tubes labels k.val)
    (fun k => AdaptedTubeWord.center atlas tubes labels (k.val+1))
    (fun k => AdaptedTubeWord.center_mem atlas tubes labels k.val)
    (fun k => AdaptedTubeWord.center_mem atlas tubes labels (k.val+1))
    (fun k => AdaptedTubeWord.reference atlas tubes labels k.val)
    (fun k => AdaptedTubeWord.reference atlas tubes labels (k.val+1))
    (fun k => AdaptedTubeWord.reference_mem atlas tubes labels k.val)
    (fun k => AdaptedTubeWord.reference_mem atlas tubes labels (k.val+1))
    (fun k => near k.val k.isLt)
  obtain ⟨H,agreement,word⟩ := word
  obtain ⟨native,identity,smooth,inverseSmooth,principal⟩ := word
  have agreementHalf : ∀ k : Fin N, ∀ z ∈ closedBall (0 : system.EuclideanModel) (radius/2), _ :=
    fun k => agreement k
  refine ⟨H,?_,native,identity,smooth,inverseSmooth,?_⟩
  · intro k _ _ z hz
    exact agreement k z (closedBall_subset_closedBall (min_le_right _ _) hz)
  · intro _ θ amplitude _continuousθ _continuousAmplitude support g formula amplitudeInside
      bounded holder cost costBound f outputSupport compactOutput output represented
    have witness := F.adapted_tubeWord_principal_witness atlas (radius := radiusT)
      (agreementRadius := radius/2) (rowRadius := rowRadius)
      (smallT.trans (min_le_right _ _)) (smallT.trans (min_le_left _ _)) tubes ε hp
      (hw.trans cap) control labels θ amplitude support H agreementHalf native identity
    apply principal (AdaptedTubeWord.center atlas tubes labels 0)
      (AdaptedTubeWord.center_mem atlas tubes labels 0)
      (AdaptedTubeWord.center atlas tubes labels N) (AdaptedTubeWord.center_mem atlas tubes labels N)
      (AdaptedTubeWord.reference atlas tubes labels 0) (AdaptedTubeWord.reference_mem atlas tubes labels 0)
      (AdaptedTubeWord.reference atlas tubes labels N) (AdaptedTubeWord.reference_mem atlas tubes labels N)
      g amplitudeInside bounded holder
    · intro z nonzero
      rw [formula z] at nonzero
      exact witness z nonzero
    · intro z
      rw [formula z]
      by_cases target : z ∈ (AdaptedTubeWord.chart atlas tubes labels 0).target
      · simp only [ChartLocalization.coordinate, ite_eq_left target]
        exact costBound _
      · simp only [ChartLocalization.coordinate, ite_eq_right target, enorm_zero]
        exact zero_le
    · exact represented

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
