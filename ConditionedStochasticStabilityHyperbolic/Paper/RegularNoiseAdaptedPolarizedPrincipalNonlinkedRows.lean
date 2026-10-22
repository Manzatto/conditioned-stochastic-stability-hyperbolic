module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedPolarizedWordGeometry
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafUniformNonlinkedRows
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafAdaptedPrincipalRows
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCompactManifold
public import LeanShared.Analysis.GlobalWordAdjointRadialBounds
public import LeanShared.Analysis.OrthogonalHalfConeGlobalWordFakeLeaves
public import LeanShared.Analysis.OrthogonalRateGlobalWordFakeLeaves
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! The same internally chosen actual noise-word family has both native
principal rows and uniform nonlinked physical rows. The principal constant
precedes word length. The nonlinked constants precede all noise controls,
chart configurations, amplitudes and input functions for a fixed length. -/
public noncomputable section
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal SchwartzMap BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
open LeanShared.OrthogonalRateGlobalWordFakeLeaves
open LeanShared.OrthogonalProductCoordinates
open AllFakeLeafModel
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

set_option maxHeartbeats 1600000 in
theorem Maps.adapted_polarized_principal_nonlinked_rows {r α : ℝ}
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
        (∀ (native : M≃ₜM), ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 native →
      ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 native.symm →
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
  have constructed :=
    F.adapted_polarized_word_geometry (b := b) (system := system)
      positiveα subunitα lower regularT backward atlas positiveStable
  rcases constructed with ⟨μ,positiveμ,contractingμ,ν,expandingν,K,positiveK,families⟩
  let : CompactSpace M := F.atlas.compactSpace
  let low : Bool → 𝓢(system.EuclideanModel,ℂ) :=
    ConeHolderAnisotropicEmbedding.lowBase outputRadial
  let high : Bool → 𝓢(system.EuclideanModel,ℂ) :=
    ConeHolderAnisotropicEmbedding.highBase outputRadial outputAngle
  have principalData := AllFakeLeafModel.exists_adapted_global_word_principal_bound
    (I := Bool) (K := K) system atlas positiveStable low high positiveK.le
  rcases principalData with ⟨rowRadius,positiveRowRadius,principalMargin,positivePrincipalMargin,A,principal⟩
  have familyData := families principalMargin positivePrincipalMargin
  rcases familyData with ⟨radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,C,Cinv,nonnegativeC,nonnegativeCinv,family⟩
  refine ⟨μ,positiveμ,contractingμ,ν,expandingν,K,positiveK,rowRadius,positiveRowRadius,A,
    radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,C,Cinv,nonnegativeC,nonnegativeCinv,?_⟩
  intro N large Z ιleaf κfreq _ _ _ _ ambientBasis planes plus cone coordinates basis i planeSame plusSame
    inputMinus inputRadial inputCutoffs amplitudeSupport compactAmplitude G₀ G₁ nonnegativeG₀ nonnegativeG₁
    inputSupport compactInput b₀ hb₀ hb₀1 t tMargin
  have sourceCone : AllFakeLeafModel.ConeData (planes i)
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2)) := by
    rw [←plusSame]
    exact cone i
  have positiveν : 0 < ν := lt_trans zero_lt_one expandingν
  obtain ⟨_,_,_,narrowLtMinus,_,_,_,_⟩ :=
    OneStepConePolarization.opening_bounds system.rate_pos system.rate_lt_one
  have uniformData := AllFakeLeafModel.exists_uniform_nonlinked_block_bound
    (E := system.EuclideanModel) (I := Z) (ι := ιleaf) (κ := κfreq)
    (Dp := ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (Dm := ProjectionConeTransversality.cone system.euclideanSecondProjection (OneStepConePolarization.minusOpening system.rate)) (Cm := inputMinus)
    (α := α) (D := K^N)
    (L := GlobalHomeomorphWordHolderBounds.holderConstant K (max C Cinv) α N)
    (G₀ := G₀) (G₁ := G₁) (K := K^N)
    (upper := 10*μ^N) (lower := (4*(ν⁻¹)^N)⁻¹)
    (narrow := ProjectionConeTransversality.cone system.euclideanSecondProjection (OneStepConePolarization.narrowOpening system.rate))
    (L₀ := amplitudeSupport) (S := inputSupport) (b := b₀)
    ambientBasis planes plus cone coordinates basis i sourceCone positiveα
    (pow_nonneg positiveK.le _) (GlobalHomeomorphWordHolderBounds.holderConstant_nonneg positiveK.le
      (le_trans nonnegativeC (le_max_left _ _)) N)
    nonnegativeG₀ nonnegativeG₁ (pow_nonneg positiveK.le _)
    (ProjectionConeRadialMargin.closed system.euclideanSecondProjection (OneStepConePolarization.narrowOpening system.rate))
    (fun v hv nonzero => ProjectionConeRadialMargin.nonzero_mem_interior system.euclideanSecondProjection
      narrowLtMinus hv nonzero)
    (fun r hr v hv => (cone i).scale r hr v hv)
    (fun r hr v hv => ProjectionConeRadialMargin.smul_mem system.euclideanSecondProjection hr hv)
    (by positivity : 0 < 10*μ^N) (by positivity : 0 < (4*(ν⁻¹)^N)⁻¹)
    outputRadial inputRadial outputAngle inputCutoffs compactAmplitude compactInput hb₀ hb₀1 t tMargin
  rcases uniformData with ⟨frequencyCutoff,remainder,nonlinked⟩
  refine ⟨frequencyCutoff,remainder,?_⟩
  intro ε hp hw control c d hc hd x y hx hy near
  have actualFamily := family ε hp hw N control c d hc hd x y hx hy near
  rcases actualFamily with ⟨H,U,S,stable,unstable,inverseBound,close,properties,fake,wordNorm,wordInverse,wordHolder,
      _inverseHolder,polarization⟩
  have regularity : 1 ≤ r := by linarith
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using regularity)
  have smooth (k : Fin N) : ContDiff ℝ 1 (H k) :=
    (properties k).2.1.differentiable.contDiff.of_le (by exact_mod_cast order)
  have inverseSmooth (k : Fin N) : ContDiff ℝ 1 (H k).symm :=
    (properties k).2.2.1.differentiable.contDiff.of_le (by exact_mod_cast order)
  refine ⟨H,U,S,stable,unstable,inverseBound,?_,properties,fake,?_⟩
  · exact principal H smooth inverseSmooth U S stable unstable inverseBound
      (fun k z => (close k z).le) (fun k : Fin N => k)
  · let W := OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k : Fin N => k) N
    have action (z v : system.EuclideanModel) (nonzero : v ≠ 0) (outside : v ∉ interior (plus i)) :
        (fderiv ℝ W z).adjoint v ∈ ProjectionConeTransversality.cone system.euclideanSecondProjection
          (OneStepConePolarization.narrowOpening system.rate) := by
      rw [plusSame] at outside
      exact ((polarization large z).2.2 v nonzero outside).1
    have lowerBound (z v : system.EuclideanModel) (outside : v ∉ interior (plus i)) :
        (4*(ν⁻¹)^N)⁻¹*‖v‖ ≤ ‖(fderiv ℝ W z).adjoint v‖ := by
      rw [plusSame] at outside
      exact (polarization large z).2.1 v outside
    have images (Γ : AllFakeLeafModel.Index (planes i)
        (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))) :
        ∃ image : AllFakeLeafModel.Index (planes i) (plus i), image.val=W '' Γ.val := by
      have stableDimension : Module.finrank ℝ (planes i)ᗮ=system.framing.stableDimension := by
        rw [planeSame,←secondPlane_eq_orthogonal,secondPlane_dimension]
        simp only [finrank_euclideanSpace,Fintype.card_fin]
      have embedded : C1Embedded (planes i) (W '' Γ.val) := by
        by_cases nonempty : Nonempty Γ.val
        · let := nonempty
          exact Γ.property.1.image_local_diffeomorphism (slope_positive _ _ sourceCone).le
            (slope_bound _ _ sourceCone Γ) W.toOpenPartialHomeomorph (subset_univ _)
            (GlobalWordNarrowProjectionBounds.prefix_contDiff H smooth (fun k : Fin N => k) N).contDiffOn
            (GlobalWordNarrowProjectionBounds.prefix_inverse_contDiff H inverseSmooth (fun k : Fin N => k) N).contDiffOn
        · have empty : Γ.val=∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            exact nonempty ⟨⟨x,hx⟩⟩
          simpa only [empty,image_empty] using embedded_empty (planes i)
      have actualFake := fake Γ.val (by simpa only [stableDimension] using Γ.property.2) N
      refine ⟨⟨W '' Γ.val,embedded,?_⟩,rfl⟩
      rw [plusSame]
      simpa only [stableDimension] using actualFake
    intro g supported gvalue gholder
    exact nonlinked W (GlobalWordNarrowProjectionBounds.prefix_contDiff H smooth (fun k : Fin N => k) N)
      (GlobalWordNarrowProjectionBounds.prefix_inverse_contDiff H inverseSmooth (fun k : Fin N => k) N)
      wordNorm (fun z w => by simpa only [dist_eq_norm] using wordHolder z w) wordInverse
      action (fun z => (polarization large z).1) lowerBound
      g supported gvalue gholder images

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
