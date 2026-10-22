module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedPolarizedPhysicalPrincipalNonlinkedRows
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafNativeTwoNormBound

/-! The actual physical principal and nonlinked rows of one internally
constructed native word are fed into the native two-norm consumer on the
full heterogeneous fake-leaf carrier. Nothing about the rows is assumed:
both callbacks of `native_two_norm_bound` are discharged by
`Maps.adapted_physical_principal_nonlinked_rows`, for the same global word,
amplitude and cost. The represented closed output remains an explicit
hypothesis on the concrete function; it is not a row estimate. -/
public noncomputable section
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal SchwartzMap BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
open LeanShared.OrthogonalRateGlobalWordFakeLeaves
open LeanShared.OrthogonalProductCoordinates
open AllFakeLeafModel BTLinkedDyadicWeights

/-- A full fake-leaf index transported along equal planes and cones keeps its leaf. -/
private theorem index_transport {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]
    [FiniteDimensional ℝ E₀] {U U' : Submodule ℝ E₀} {C C' : Set E₀} (hU : U = U') (hC : C = C')
    (Γ : Index U C) : ∃ Γ' : Index U' C', Γ'.val = Γ.val := by
  subst hU; subst hC; exact ⟨Γ, rfl⟩

private theorem volume_transport {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]
    [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] {U U' : Submodule ℝ E₀}
    (hU : U = U') (Γ : Set E₀) :
    EmbeddedSubmanifoldVolume.volume U volume Γ = EmbeddedSubmanifoldVolume.volume U' volume Γ := by
  subst hU; rfl

universe uZ uL uK

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

set_option maxHeartbeats 3200000 in
theorem Maps.adapted_polarized_native_two_norm_rows {r α : ℝ}
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
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ, 0 < η ∧ ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∃ C Cinv : ℝ, 0 ≤ C ∧ 0 ≤ Cinv ∧
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
      ∀ control : Fin N → cube (ι := ι) ε,
      ∀ c d : Fin N → Λ, (∀ k, c k ∈ atlas.centers) → (∀ k, d k ∈ atlas.centers) →
      ∀ x y : Fin N → Λ, ∀ hx : ∀ k, x k ∈ atlas.patch (c k),
      ∀ hy : ∀ k, y k ∈ atlas.patch (d k), (∀ k, dist (T (x k).val) (y k).val < η) →
      ∃ H : Fin N → system.EuclideanModel ≃ₜ system.EuclideanModel,
        (∀ k,
          let L := ContinuousCenteredFrameCharts.chartFrame (c k).val (x k).val (atlas.inside (c k) (hx k)).2
            (system.euclideanReferenceFrame (c k) ⟨x k, atlas.inside (c k) (hx k)⟩)
          let R := ContinuousCenteredFrameCharts.chartFrame (d k).val (y k).val (atlas.inside (d k) (hy k)).2
            (system.euclideanReferenceFrame (d k) ⟨y k, atlas.inside (d k) (hy k)⟩)
          ∀ z ∈ closedBall 0 (radius/2), H k z = centered L R ((chartAt E (c k).val) (x k).val)
            ((chartAt E (d k).val) (y k).val)
            (chartAt E (d k).val ∘ F.family ε (control k).val ∘ (chartAt E (c k).val).symm) z) ∧
        ∃ native : M≃ₜM,
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
        ∀ g : system.EuclideanModel →ᵇ ℂ,
          tsupport (fun w => g w) ⊆ amplitudeSupport →
          (∀ w, ‖g w‖ ≤ G₀) → (∀ z w, ‖g z-g w‖ ≤ G₁*dist z w^α) →
          (∀ z, g z≠0 → ‖z‖≤rowRadius ∧ ‖W z‖≤rowRadius ∧
            native (system.normalizedProjectionPoint c sourceRef z) =
              system.normalizedProjectionPoint d targetRef (W z) ∧
            (W : system.EuclideanModel→system.EuclideanModel) =ᶠ[𝓝 z]
              centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
                (chartAt E d.val ∘ native ∘ (chartAt E c.val).symm)) →
          ∀ cost : ℝ≥0,
          (∀ z, ‖g z‖ₑ≤(cost:ℝ≥0∞)*ENNReal.ofReal
            (((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) native
              (system.normalizedProjectionPoint c sourceRef z)).toLinearMap.domRestrict
              (b.hyperbolic.normedAdaptedProjection.unstable
                (system.normalizedProjectionPoint c sourceRef z))).normDet)) →
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
  have combined := Maps.adapted_polarized_physical_principal_nonlinked_rows.{_, _, _, uZ, uL, uK} F (b := b) (system := system)
      positiveα subunitα lower regularT backward atlas positiveStable outputRadial outputAngle
  rcases combined with ⟨μ,positiveμ,contractingμ,ν,expandingν,K,positiveK,rowRadius,positiveRowRadius,A,
    radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,C,Cinv,nonnegativeC,nonnegativeCinv,family⟩
  refine ⟨μ,positiveμ,contractingμ,ν,expandingν,K,positiveK,rowRadius,positiveRowRadius,A,?_⟩
  refine ⟨radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,C,Cinv,nonnegativeC,nonnegativeCinv,?_⟩
  intro N large Z ιleaf κfreq _ _ _ _ ambientBasis planes plus cone coordinates basis i planeSame plusSame
    inputMinus inputRadial inputCutoffs amplitudeSupport compactAmplitude G₀ G₁ nonnegativeG₀ nonnegativeG₁
    inputSupport compactInput b₀ hb₀ hb₀1 t s loss ht hs hLoss gap margin
  have rowsAll := family N large ambientBasis planes plus cone
    coordinates basis i planeSame plusSame inputRadial inputCutoffs compactAmplitude nonnegativeG₀ nonnegativeG₁
    compactInput hb₀ hb₀1
  have rowsT := rowsAll (fun sign => exponent t s sign-loss)
    (fun sign => (sub_le_self _ hLoss).trans (margin sign))
  obtain ⟨frequencyCutoff,remainder,rows⟩ := rowsT
  refine ⟨frequencyCutoff,remainder,?_⟩
  intro ε hp hw control c d hc hd x y hx hy near
  have word := rows ε hp hw control c d hc hd x y hx hy near
  obtain ⟨H,word⟩ := word
  obtain ⟨U,S,stable,unstable,inverseBound,nativeRows,properties,fake,nonlinkedRows⟩ := word
  obtain ⟨native,identity,smooth,inverseSmooth,principalRows⟩ := nativeRows
  refine ⟨H,fun k => (properties k).1,native,identity,smooth,inverseSmooth,?_⟩
  intro c' hc' d' hd' x' hx' y' hy' sourceRef targetRef W L R g amplitude bounded holder support
    cost costBound f outputSupport compactOutput output represented
  have positiveν : 0 < ν := by linarith
  have compactG : HasCompactSupport (g : system.EuclideanModel → ℂ) :=
    compactAmplitude.of_isClosed_subset (isClosed_tsupport _) amplitude
  have coneEq : ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2) =
      ProjectionConeTransversality.cone (firstPlane system.euclideanDimension).starProjection (1/2) := by
    rw [firstPlane_projection]; rfl
  apply AllFakeLeafHolderCoreBounds.native_two_norm_bound planes plus cone coordinates basis i i rfl rfl
    inputRadial outputRadial inputCutoffs.original outputAngle compactInput compactOutput hb₀ hb₀1 f
    W W.continuous g g.continuous compactG output represented t s loss α (10*μ^N) ((4*(ν⁻¹)^N)⁻¹)
    ht hs hLoss gap (by positivity) (by positivity) A cost remainder frequencyCutoff margin
  · intro j k Γ B inputBound
    obtain ⟨Γ',hΓ'⟩ := index_transport planeSame (plusSame.trans coneEq) Γ
    have movedBound : ∀ Δ' : Index (firstPlane system.euclideanDimension)
        (ProjectionConeTransversality.cone (firstPlane system.euclideanDimension).starProjection (1/2)),
        ∫⁻ z, ‖ConeFourierBlocks.block (ConeDyadicSymbols.symbols inputRadial inputCutoffs.original k)
          f.val z‖ₑ ∂EmbeddedSubmanifoldVolume.volume (firstPlane system.euclideanDimension) volume Δ'.val ≤ B := by
      intro Δ'
      obtain ⟨Δ,hΔ⟩ := index_transport planeSame.symm (plusSame.trans coneEq).symm Δ'
      rw [← volume_transport planeSame, ← hΔ]
      exact inputBound Δ
    have row := principalRows c' hc' d' hd' x' hx' y' hy' volume g _ g.continuous.measurable
      (ConeFourierBlocks.block _ f.val).continuous.measurable support cost B movedBound costBound j Γ'
    rw [volume_transport planeSame, ← hΓ']
    exact row
  · intro j k Γ large unlinked
    obtain ⟨Γ',hΓ'⟩ := index_transport rfl plusSame Γ
    rw [← hΓ']
    exact nonlinkedRows g amplitude bounded holder j k large unlinked f Γ'

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
