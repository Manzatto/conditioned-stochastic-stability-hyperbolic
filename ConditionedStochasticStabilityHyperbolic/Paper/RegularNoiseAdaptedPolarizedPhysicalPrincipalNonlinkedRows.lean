module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedPolarizedPrincipalNonlinkedRows
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseFiniteDiffeomorphismWords
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafUniformNonlinkedRows
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafAdaptedPrincipalRows
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCompactManifold
public import LeanShared.Analysis.GlobalWordAdjointRadialBounds
public import LeanShared.Analysis.OrthogonalHalfConeGlobalWordFakeLeaves
public import LeanShared.Analysis.OrthogonalRateGlobalWordFakeLeaves
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! Both proved physical row estimates act on one internally constructed
actual manifold word. Its literal identity and its two-sided C1 regularity
are derived from the original perturbation hypotheses. -/
public noncomputable section
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal SchwartzMap BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
open LeanShared.OrthogonalRateGlobalWordFakeLeaves
open LeanShared.OrthogonalProductCoordinates
open AllFakeLeafModel

private theorem native_word_data
    {E₀ M₀ noiseI : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [MetricSpace M₀] [ChartedSpace E₀ M₀] [IsManifold (𝓘(ℝ,E₀)) ∞ M₀] [Fintype noiseI]
    {T₀ : M₀ ≃ₜ M₀} {r₀ : ℝ} (F₀ : Maps (E := E₀) (ι := noiseI) T₀ r₀)
    (regularity : 1 ≤ r₀) (deterministic : ContMDiff (𝓘(ℝ,E₀)) (𝓘(ℝ,E₀)) 1 T₀)
    (inverse : MDifferentiable (𝓘(ℝ,E₀)) (𝓘(ℝ,E₀)) T₀.symm) :
    ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F₀.window ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ N : ℕ, ∀ control : Fin N → cube (ι := noiseI) ε,
      ∃ native : M₀ ≃ₜ M₀,
        (native : M₀ → M₀) = CylinderPrincipalCoefficient.prefixOrbit
          (fun k : Fin N => F₀.family ε (control k).val) (fun k => k) N ∧
        ContMDiff (𝓘(ℝ,E₀)) (𝓘(ℝ,E₀)) 1 native ∧
        ContMDiff (𝓘(ℝ,E₀)) (𝓘(ℝ,E₀)) 1 native.symm := by
  obtain ⟨cutoff,positive,cap,words⟩ := F₀.finite_diffeomorphism_words regularity deterministic inverse
  refine ⟨cutoff,positive,cap,?_⟩
  intro ε hp hw N control
  obtain ⟨native,identity,smooth,backward,_⟩ := words ε hp hw N control
  exact ⟨native,identity,smooth,backward⟩

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

set_option maxHeartbeats 1600000 in
theorem Maps.adapted_polarized_physical_principal_nonlinked_rows {r α : ℝ}
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
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∃ ν : ℝ, 1 < ν ∧
    ∃ K : ℝ, 0 < K ∧ ∃ rowRadius : ℝ, 0 < rowRadius ∧ ∃ A : ℝ≥0,
    ∃ radius > 0, ∃ η > 0, ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∃ C Cinv : ℝ, 0 ≤ C ∧ 0 ≤ Cinv ∧
      ∀ N : ℕ, 0 < N →
      ∀ {Z ιleaf κfreq : Type*}, ∀ [Finite Z], ∀ [Fintype ιleaf], ∀ [DecidableEq ιleaf], ∀ [Fintype κfreq],
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
      (t : Bool → ℝ) (tMargin : ∀ sign, t sign ≤ b₀),
      ∃ frequencyCutoff : ℕ, ∃ remainder : ℝ≥0,
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff →
      ∀ control : Fin N → cube (ι := ι) ε,
      ∀ c d : Fin N → Λ, (∀ k, c k ∈ atlas.centers) → (∀ k, d k ∈ atlas.centers) →
      ∀ x y : Fin N → Λ, ∀ hx : ∀ k, x k ∈ atlas.patch (c k),
      ∀ hy : ∀ k, y k ∈ atlas.patch (d k), (∀ k, dist (T (x k).val) (y k).val < η) →
      ∃ H : Fin N → system.EuclideanModel ≃ₜ system.EuclideanModel,
        ∃ U : Fin N → (EuclideanSpace ℝ (Fin system.framing.unstableDimension)) ≃L[ℝ] (EuclideanSpace ℝ (Fin system.framing.unstableDimension)),
        ∃ S : Fin N → (EuclideanSpace ℝ (Fin system.framing.stableDimension)) ≃L[ℝ] (EuclideanSpace ℝ (Fin system.framing.stableDimension)),
        (∀ k, ‖(S k).toContinuousLinearMap‖ ≤ system.rate) ∧
        (∀ k, ‖(U k).symm.toContinuousLinearMap‖ ≤ system.rate) ∧
        (∀ k, ‖(system.euclideanDiagonal (U k) (S k)).symm.toContinuousLinearMap‖ ≤ K) ∧
        (∃ native : M≃ₜM,
      (native : M→M) = CylinderPrincipalCoefficient.prefixOrbit
        (fun k : Fin N => F.family ε (control k).val) (fun k => k) N ∧
      ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 native ∧
      ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 native.symm ∧
      ∀ c∈atlas.centers, ∀ d∈atlas.centers, ∀ x (hx : x∈atlas.patch c), ∀ y (hy : y∈atlas.patch d),
      let sourceRef : system.frameDomain c := ⟨x,atlas.inside c hx⟩
      let targetRef : system.frameDomain d := ⟨y,atlas.inside d hy⟩
      let W := prefixHomeomorph H (fun k : Fin N => k) N
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c sourceRef)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.euclideanReferenceFrame d targetRef)
      let P := firstPlane system.euclideanDimension
      ∀ μ : Measure P, ∀ [μ.IsAddHaarMeasure], ∀ g u : system.EuclideanModel→ℂ,
      Measurable g → Measurable u →
      (∀ z, g z≠0 → ‖z‖≤rowRadius ∧ ‖W z‖≤rowRadius ∧
        native (system.normalizedProjectionPoint c sourceRef z)=system.normalizedProjectionPoint d targetRef (W z) ∧
        (W : system.EuclideanModel→system.EuclideanModel) =ᶠ[𝓝 z]
          centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
            (chartAt E d.val ∘ native ∘ (chartAt E c.val).symm)) →
      ∀ cost : ℝ≥0, ∀ B : ℝ≥0∞,
      (∀ Δ : Index P (ProjectionConeTransversality.cone P.starProjection (1/2)),
        ∫⁻ z, ‖u z‖ₑ ∂EmbeddedSubmanifoldVolume.volume P μ Δ.val≤B) →
      (∀ z, ‖g z‖ₑ≤(cost:ℝ≥0∞)*ENNReal.ofReal
        (((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) native (system.normalizedProjectionPoint c sourceRef z)).toLinearMap.domRestrict
          (b.hyperbolic.normedAdaptedProjection.unstable (system.normalizedProjectionPoint c sourceRef z))).normDet)) →
      ∀ j : ℕ×Bool, ∀ Γ : Index P (ProjectionConeTransversality.cone P.starProjection (1/2)),
        (∫⁻ z, ‖∫ w, DyadicSymbols.kernel (ConeHolderAnisotropicEmbedding.lowBase outputRadial)
          (ConeHolderAnisotropicEmbedding.highBase outputRadial outputAngle) j (z-w)*g w*u (W w)‖ₑ
          ∂EmbeddedSubmanifoldVolume.volume P μ Γ.val)≤(A:ℝ≥0∞)*((cost:ℝ≥0∞)*B)) ∧
        (∀ k,
          let L := ContinuousCenteredFrameCharts.chartFrame (c k).val (x k).val (atlas.inside (c k) (hx k)).2
            (system.euclideanReferenceFrame (c k) ⟨x k, atlas.inside (c k) (hx k)⟩)
          let R := ContinuousCenteredFrameCharts.chartFrame (d k).val (y k).val (atlas.inside (d k) (hy k)).2
            (system.euclideanReferenceFrame (d k) ⟨y k, atlas.inside (d k) (hy k)⟩)
          let h := centered L R ((chartAt E (c k).val) (x k).val) ((chartAt E (d k).val) (y k).val)
            (chartAt E (d k).val ∘ F.family ε (control k).val ∘ (chartAt E (c k).val).symm)
          (∀ z ∈ closedBall 0 (radius/2), H k z = h z) ∧
          FractionalManifoldRegularity.Regular (E := system.EuclideanModel) (F := system.EuclideanModel) r (H k) ∧
          FractionalManifoldRegularity.Regular (E := system.EuclideanModel) (F := system.EuclideanModel) r (H k).symm ∧
          (∀ z, ‖fderiv ℝ (H k) z‖ ≤ K) ∧
          (∀ z, ‖fderiv ℝ (H k).symm z‖ ≤ K) ∧
          (∀ z w, ‖fderiv ℝ (H k) z-fderiv ℝ (H k) w‖ ≤ C*‖z-w‖^α) ∧
          (∀ z w, ‖fderiv ℝ (H k).symm z-fderiv ℝ (H k).symm w‖ ≤ Cinv*‖z-w‖^α)) ∧
        (∀ Γ : Set system.EuclideanModel,
          FakeLeafGeometry.leafError
            (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
            system.framing.stableDimension Γ = 0 → ∀ n : ℕ,
          FakeLeafGeometry.leafError
            (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
            system.framing.stableDimension
            (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) n '' Γ) = 0) ∧
        ∀ g : system.EuclideanModel →ᵇ ℂ,
          tsupport (fun w => g w) ⊆ amplitudeSupport →
          (∀ w, ‖g w‖ ≤ G₀) → (∀ z w, ‖g z-g w‖ ≤ G₁*dist z w^α) →
          ∀ (j k : ℕ × Bool), frequencyCutoff < max j.1 k.1 →
          ¬ BTLinkedDyadicWeights.linked (BTLinkedDyadicWeights.plusThreshold (10*μ^N))
            (BTLinkedDyadicWeights.minusThreshold ((4*(ν⁻¹)^N)⁻¹)) j k →
          ∀ f : SchwartzJetSpace.supportedCore inputSupport,
          ∀ Γ : AllFakeLeafModel.Index (planes i)
            (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2)),
          (∫⁻ z, ‖∫ w, FourierSchwartzKernel.kernel (ConeDyadicSymbols.symbols outputRadial outputAngle j) (z-w)*
            g w*ConeFourierBlocks.block (ConeDyadicSymbols.symbols inputRadial inputCutoffs.original k) f.val
              (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N w)‖ₑ
            ∂EmbeddedSubmanifoldVolume.volume (planes i) volume Γ.val) ≤
            (remainder : ℝ≥0∞)*ENNReal.ofReal ((2:ℝ)^(-α*(max j.1 k.1:ℕ)))*
              (ENNReal.ofReal ((2:ℝ)^(-(t k.2*k.1)))*
                ENNReal.ofReal ‖AllFakeLeafHolderCoreBounds.coreBlocks planes plus cone coordinates basis
                  inputRadial inputCutoffs.original compactInput hb₀ hb₀1 t tMargin i f‖) := by
  let : CompactSpace M := F.atlas.compactSpace
  have regularity : 1 ≤ r := by linarith
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using regularity)
  have deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T :=
    regularT.differentiable.of_le (by exact_mod_cast order)
  have nativeData := native_word_data (E₀ := E) (M₀ := M) (noiseI := ι) (T₀ := T) (r₀ := r) F
    regularity deterministic (backward.mdifferentiable one_ne_zero)
  rcases nativeData with ⟨nativeCutoff,positiveNativeCutoff,nativeCap,nativeWords⟩
  have combined := F.adapted_polarized_principal_nonlinked_rows (b := b) (system := system)
    positiveα subunitα lower regularT backward atlas positiveStable outputRadial outputAngle
  rcases combined with ⟨μ,positiveμ,contractingμ,ν,expandingν,K,positiveK,rowRadius,positiveRowRadius,A,
    radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,C,Cinv,nonnegativeC,nonnegativeCinv,family⟩
  refine ⟨μ,positiveμ,contractingμ,ν,expandingν,K,positiveK,rowRadius,positiveRowRadius,A,
    radius,positiveRadius,η,positiveη,min cutoff nativeCutoff,lt_min positiveCutoff positiveNativeCutoff,
    (min_le_left _ _).trans cap,C,Cinv,nonnegativeC,nonnegativeCinv,?_⟩
  intro N large Z ιleaf κfreq _ _ _ _ ambientBasis planes plus cone coordinates basis i planeSame plusSame
    inputMinus inputRadial inputCutoffs amplitudeSupport compactAmplitude G₀ G₁ nonnegativeG₀ nonnegativeG₁
    inputSupport compactInput b₀ hb₀ hb₀1 t tMargin
  have uniformData := family N large (Z := Z) (ιleaf := ιleaf) (κfreq := κfreq)
    (inputMinus := inputMinus) (amplitudeSupport := amplitudeSupport) (G₀ := G₀) (G₁ := G₁)
    (inputSupport := inputSupport) (b₀ := b₀) ambientBasis planes plus cone
    coordinates basis i planeSame plusSame inputRadial inputCutoffs compactAmplitude nonnegativeG₀ nonnegativeG₁
    compactInput hb₀ hb₀1 t tMargin
  rcases uniformData with ⟨frequencyCutoff,remainder,allConfigurations⟩
  refine ⟨frequencyCutoff,remainder,?_⟩
  intro ε hp hw control
  have nativeSmall : ε ≤ nativeCutoff := hw.trans (min_le_right _ _)
  have nativeAtWord := nativeWords ε hp nativeSmall N control
  rcases nativeAtWord with ⟨native,identity,smooth,inverseSmooth⟩
  intro c d hc hd x y hx hy near
  obtain ⟨H,U,S,stable,unstable,inverseBound,rows,properties,fake,nonlinked⟩ :=
    allConfigurations ε hp (hw.trans (min_le_left _ _)) control c d hc hd x y hx hy near
  refine ⟨H,U,S,stable,unstable,inverseBound,⟨native,identity,smooth,inverseSmooth,?_⟩,
    properties,fake,nonlinked⟩
  apply rows native smooth inverseSmooth

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
