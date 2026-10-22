module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafIntrinsicPrincipalRows
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafOrthogonalWordImages
public import LeanShared.Dynamics.HyperbolicAdaptedGlobalProjection
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanNativeJacobian
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanDecodeRadius
public import LeanShared.Geometry.DiffeomorphismDifferential
public import LeanShared.Analysis.UniformGlobalWordNarrowProjectionBounds

/-! The actual adapted geometry produces principal rows. The only amplitude
cost is the literal native unstable determinant; the endpoint comparison,
source projector, two slopes and full leaf-image family are constructed. -/
public noncomputable section
universe uG
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared HyperbolicBasicSet HyperbolicAdaptedPatchSystem OrthogonalProductCoordinates
open CenteredManifoldCoordinates OrthogonalRateGlobalWordFakeLeaves
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M≃ₜM} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem exists_adapted_global_word_principal_bound [Fintype I] (system : PatchSystem b) (atlas : ChartAtlas system)
    (positiveStable : 0<system.framing.stableDimension)
    (low high : I→𝓢(system.EuclideanModel,ℂ)) {K : ℝ} (nonnegativeK : 0≤K) :
    ∃ radius : ℝ, 0<radius ∧ ∃ ε : ℝ, 0<ε ∧ ∃ A : ℝ≥0,
      ∀ {G : Type uG}, ∀ (H : G→system.EuclideanModel≃ₜsystem.EuclideanModel)
      (_smooth : ∀ g, ContDiff ℝ 1 (H g)) (_inverseSmooth : ∀ g, ContDiff ℝ 1 (H g).symm)
      (U : G→EuclideanSpace ℝ (Fin system.framing.unstableDimension)≃L[ℝ]
        EuclideanSpace ℝ (Fin system.framing.unstableDimension))
      (S : G→EuclideanSpace ℝ (Fin system.framing.stableDimension)≃L[ℝ]
        EuclideanSpace ℝ (Fin system.framing.stableDimension)),
      (∀ g, ‖(S g).toContinuousLinearMap‖≤system.rate) →
      (∀ g, ‖(U g).symm.toContinuousLinearMap‖≤system.rate) →
      (∀ g, ‖(system.euclideanDiagonal (U g) (S g)).symm.toContinuousLinearMap‖≤K) →
      (∀ g z, ‖fderiv ℝ (H g) z-(system.euclideanDiagonal (U g) (S g)).toContinuousLinearMap‖≤ε) →
      ∀ {N : ℕ} (word : Fin N→G),
      ∀ (native : M≃ₜM), ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 native →
      ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 native.symm →
      ∀ c∈atlas.centers, ∀ d∈atlas.centers, ∀ x (hx : x∈atlas.patch c), ∀ y (hy : y∈atlas.patch d),
      let sourceRef : system.frameDomain c := ⟨x,atlas.inside c hx⟩
      let targetRef : system.frameDomain d := ⟨y,atlas.inside d hy⟩
      let W := prefixHomeomorph H word N
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c sourceRef)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.euclideanReferenceFrame d targetRef)
      let P := firstPlane system.euclideanDimension
      ∀ μ : Measure P, ∀ [μ.IsAddHaarMeasure], ∀ g u : system.EuclideanModel→ℂ,
      Measurable g → Measurable u →
      (∀ z, g z≠0 → ‖z‖≤radius ∧ ‖W z‖≤radius ∧
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
      ∀ j : ℕ×I, ∀ Γ : Index P (ProjectionConeTransversality.cone P.starProjection (1/2)),
        (∫⁻ z, ‖∫ w, DyadicSymbols.kernel low high j (z-w)*g w*u (W w)‖ₑ
          ∂EmbeddedSubmanifoldVolume.volume P μ Γ.val)≤(A:ℝ≥0∞)*((cost:ℝ≥0∞)*B) := by
  classical
  let P := firstPlane system.euclideanDimension
  have stableDimension : Module.finrank ℝ Pᗮ=system.framing.stableDimension := by
    rw [←secondPlane_eq_orthogonal,secondPlane_dimension]
    simp only [finrank_euclideanSpace,Fintype.card_fin]
  have unstableDimension : Module.finrank ℝ P=system.framing.unstableDimension := by
    rw [firstPlane_dimension]
    simp only [finrank_euclideanSpace,Fintype.card_fin]
  have positiveDimension : 0<Module.finrank ℝ (EuclideanSpace ℝ (Fin system.framing.stableDimension)) := by
    simpa only [finrank_euclideanSpace,Fintype.card_fin] using positiveStable
  have firstEq : P.starProjection=system.euclideanFirstProjection := firstPlane_projection system.euclideanDimension
  have secondEq : Pᗮ.starProjection=system.euclideanSecondProjection := orthogonal_firstPlane_projection system.euclideanDimension
  have cone := half_cone_data P (by rwa [stableDimension])
  obtain ⟨A,rows⟩ := exists_intrinsic_principal_kernel_bound low high P
  obtain ⟨η,positiveη,projections⟩ := system.global_normalized_projection_data atlas
  obtain ⟨Rj,positiveRj,C,positiveC,jacobian⟩ := atlas.euclidean_native_jacobian_bound
  obtain ⟨Rd,positiveRd,decode⟩ := atlas.euclidean_decode_radius η positiveη
  obtain ⟨εn,positiveεn,narrow⟩ := GlobalWordNarrowProjectionBounds.exists_uniform_budget_all_families
     system.rate_pos system.rate_lt_one system.euclideanDimension
  have positiveHalf := (OrthogonalDiagonalRatePerturbation.radius_bounds system.rate K
    system.rate_pos system.rate_lt_one nonnegativeK).1
  let ε := min εn (OrthogonalDiagonalRatePerturbation.radius system.rate K)
  let radius := min Rj Rd
  let Jcost : ℝ≥0 := ⟨GraphJacobian.densityBound (ι := Fin system.framing.unstableDimension) C*
    GraphJacobian.densityBound (ι := Fin system.framing.unstableDimension) C,
    mul_nonneg (GraphJacobian.densityBound_nonneg _) (GraphJacobian.densityBound_nonneg _)⟩
  refine ⟨radius,lt_min positiveRj positiveRd,ε,lt_min positiveεn positiveHalf,A*Jcost,?_⟩
  intro G H smooth inverseSmooth U S stable unstable inverseBound close N word native nativeSmooth nativeInverse
    c hc d hd x hx y hy
  dsimp only
  let sourceRef : system.frameDomain c := ⟨x,atlas.inside c hx⟩
  let targetRef : system.frameDomain d := ⟨y,atlas.inside d hy⟩
  let W := prefixHomeomorph H word N
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.euclideanReferenceFrame c sourceRef)
  let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
    (system.euclideanReferenceFrame d targetRef)
  intro μ _ g u measurableG measurableU tracking cost B leafBound nativeCost j Γ
  have forward : ContDiff ℝ 1 W := GlobalWordNarrowProjectionBounds.prefix_contDiff H smooth word N
  have backward : ContDiff ℝ 1 W.symm := GlobalWordNarrowProjectionBounds.prefix_inverse_contDiff H inverseSmooth word N
  let differential (z : system.EuclideanModel) := HomeomorphDerivativeEquivalence.derivative W
    (forward.differentiable one_ne_zero) (backward.differentiable one_ne_zero) z
  let source := system.globalNormalizedProjection η c sourceRef
  let target : system.EuclideanModel→system.EuclideanModel→L[ℝ]system.EuclideanModel := fun _ => system.euclideanSecondProjection
  have projection := projections c hc x hx
  have sourceClose (z : system.EuclideanModel) : ‖source z-Pᗮ.starProjection‖≤(1/64:ℝ) := by
    rw [secondEq]
    exact (projection.1 z).1
  have sourceRank (z : system.EuclideanModel) : Module.finrank ℝ (source z).ker=Module.finrank ℝ P :=
    (projection.1 z).2.2.2.1.trans unstableDimension.symm
  have targetRank (z : system.EuclideanModel) : Module.finrank ℝ (target z).range=Module.finrank ℝ Pᗮ := by
    change Module.finrank ℝ system.euclideanSecondProjection.range=Module.finrank ℝ Pᗮ
    rw [←secondEq,Submodule.range_starProjection]
  have targetIdem (z v : system.EuclideanModel) : target z (target z v)=target z v := by
    change system.euclideanSecondProjection (system.euclideanSecondProjection v)=system.euclideanSecondProjection v
    rw [←secondEq]
    exact congrArg (fun Q : system.EuclideanModel→L[ℝ]system.EuclideanModel => Q v) Pᗮ.isIdempotentElem_starProjection.eq
  have slopes (z : system.EuclideanModel) := narrow H smooth inverseSmooth U
    (fun a => (S a).toContinuousLinearMap) stable unstable
    (fun a w => (close a w).trans (min_le_left _ _)) word z (source z)
    (by change ‖source z-system.euclideanSecondProjection‖≤_; exact (projection.1 z).1)
  have images (Δ : Index P (ProjectionConeTransversality.cone P.starProjection (1/2))) :
      ∃ image : Index P (ProjectionConeTransversality.cone P.starProjection (1/2)), image.val=W '' Δ.val :=
    actual_half_word_image_index system.euclideanDimension positiveDimension system.rate_pos system.rate_lt_one nonnegativeK
      U S stable unstable inverseBound H smooth inverseSmooth
      (fun a w => (close a w).trans (min_le_right _ _)) word N Δ
  have intrinsic (z : system.EuclideanModel) : ‖g z‖ₑ≤((cost*Jcost:ℝ≥0):ℝ≥0∞)*
      ENNReal.ofReal (((differential z).toLinearMap.domRestrict (source z).ker).normDet) := by
    by_cases zero : g z=0
    · rw [zero,enorm_zero]
      exact bot_le
    · obtain ⟨smallZ,smallW,image,agreement⟩ := tracking z zero
      have decodeFacts := decode c hc x hx z (smallZ.trans (min_le_right _ _))
      have near : dist x.val (system.normalizedProjectionPoint c sourceRef z)<η := by
        simpa only [PatchSystem.normalizedProjectionPoint,dist_comm] using decodeFacts.2
      obtain ⟨insidePlane,plane⟩ := projection.2 z near
      let p := system.normalizedProjectionPoint c sourceRef z
      let Q := b.hyperbolic.normedAdaptedProjection.unstable p
      let encode := CenteredTangentJacobianComparison.encoding (chartAt E c.val)
        (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) p insidePlane L
      have planeActual : (source z).ker=Q.map encode.toLinearMap := plane
      have dimensionQ : Module.finrank ℝ Q=system.framing.unstableDimension := by
        have same := encode.toLinearEquiv.finrank_map_eq Q
        rw [←planeActual] at same
        exact same.symm.trans ((projection.1 z).2.2.2.1)
      let D := DiffeomorphismDifferential.differential native
        (nativeSmooth.mdifferentiable one_ne_zero) (nativeInverse.mdifferentiable one_ne_zero) p
      have nativeDifferential : D.toContinuousLinearMap=mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) native p := by
        apply ContinuousLinearMap.ext
        intro v
        exact DiffeomorphismDifferential.differential_apply native
          (nativeSmooth.mdifferentiable one_ne_zero) (nativeInverse.mdifferentiable one_ne_zero) p v
      obtain ⟨insideJacobian,estimate⟩ := jacobian c hc d hd x hx y hy z (W z)
        (smallZ.trans (min_le_left _ _)) (smallW.trans (min_le_left _ _)) native image
        (nativeSmooth.mdifferentiable one_ne_zero p) D nativeDifferential Q W agreement
      have encodedRange : ((encode.toContinuousLinearMap.comp Q.subtypeL).toLinearMap.range)=(source z).ker := by
        rw [planeActual]
        ext v
        constructor
        · rintro ⟨q,rfl⟩
          exact ⟨q.val,q.property,rfl⟩
        · rintro ⟨q,hq,rfl⟩
          exact ⟨⟨q,hq⟩,rfl⟩
      have comparison : ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) native p).toLinearMap.domRestrict Q).normDet≤
          (Jcost:ℝ)*((differential z).toLinearMap.domRestrict (source z).ker).normDet := by
        change (D.toContinuousLinearMap.toLinearMap.domRestrict Q).normDet≤_ at estimate
        rw [nativeDifferential] at estimate
        have densityEq : GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ Q)) C =
            GraphJacobian.densityBound (ι := Fin system.framing.unstableDimension) C :=
          congrArg (fun n : ℕ => GraphJacobian.densityBound (ι := Fin n) C) dimensionQ
        change ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) native p).toLinearMap.domRestrict Q).normDet≤
          (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ Q)) C*
            GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ Q)) C)*
              ((fderiv ℝ W z).toLinearMap.domRestrict
                (encode.toContinuousLinearMap.comp Q.subtypeL).toLinearMap.range).normDet at estimate
        have scalar : GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ Q)) C*
            GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ Q)) C ≤ (Jcost:ℝ) :=
          (congrArg (fun a : ℝ => a*a) densityEq).le
        have bounded := estimate.trans (mul_le_mul_of_nonneg_right scalar (LinearMap.normDet_nonneg _))
        have planeJacobian := congrArg (fun A : Submodule ℝ system.EuclideanModel =>
          ((fderiv ℝ W z).toLinearMap.domRestrict A).normDet) encodedRange
        have atKernel := bounded.trans_eq (congrArg (fun a : ℝ => (Jcost:ℝ)*a) planeJacobian)
        have globalDifferential : (differential z).toContinuousLinearMap=fderiv ℝ W z :=
          HomeomorphDerivativeEquivalence.derivative_coe W _ _ z
        have globalJacobian := congrArg (fun A : system.EuclideanModel→L[ℝ]system.EuclideanModel =>
          (A.toLinearMap.domRestrict (source z).ker).normDet) globalDifferential
        exact atKernel.trans_eq (congrArg (fun a : ℝ => (Jcost:ℝ)*a) globalJacobian.symm)
      refine (nativeCost z).trans ((mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal comparison)
        (show 0≤(cost:ℝ≥0∞) from bot_le)).trans_eq ?_)
      rw [ENNReal.ofReal_mul Jcost.coe_nonneg,ENNReal.ofReal_coe_nnreal]
      simp only [ENNReal.coe_mul,mul_assoc]
  have bound := rows (ProjectionConeTransversality.cone P.starProjection (1/2)) cone cone μ W.toOpenPartialHomeomorph
    forward.contDiffOn backward.contDiffOn W.continuous.measurable univ isOpen_univ (subset_refl _)
    (fun Δ _ => images Δ) source target differential
    (fun z _ => (HomeomorphDerivativeEquivalence.derivative_coe W _ _ z).symm)
    (fun z _ => sourceClose z)
    (fun z _ => by change ‖system.euclideanSecondProjection-Pᗮ.starProjection‖≤_; rw [secondEq,sub_self,norm_zero]; norm_num)
    (fun z _ => sourceRank z) (fun z _ => targetRank z) (fun z _ => targetIdem z)
    (fun z _ => by rw [firstEq,secondEq]; exact (slopes z).1)
    (fun z _ => by rw [firstEq,secondEq]; exact (slopes z).2)
    g u measurableG measurableU (fun z outside => False.elim (outside (mem_univ z)))
    (cost*Jcost) B leafBound (fun z _ => intrinsic z) j Γ
  exact bound.trans_eq (by simp only [ENNReal.coe_mul]; ring)

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
