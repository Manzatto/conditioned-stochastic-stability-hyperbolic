module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedRetainedHalfWordGeometry
public import LeanShared.Analysis.GlobalWordOneStepPolarization
public import LeanShared.Analysis.GlobalHomeomorphWordHolderBounds
public import LeanShared.Analysis.GlobalWordAdjointRadialBounds
public import LeanShared.Analysis.OrthogonalHalfConeGlobalWordFakeLeaves
public import LeanShared.Analysis.OrthogonalRateGlobalWordFakeLeaves
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones

/-! One internally constructed original-noise family retains any caller's
principal tolerance and also has actual full-word Holder bounds and, for
every word length at least one, the one-step-adapted polarization required
by nonlinked rows: frequencies outside the plus half cone are sent into the
narrow cone `cone(second, 1+q²)`, strictly inside the minus cone
`cone(second, (3+q²)/2)`. No length threshold is needed. -/
public noncomputable section
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

theorem Maps.adapted_polarized_word_geometry {r α : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (atlas : ChartAtlas system) (positiveStable : 0 < system.framing.stableDimension) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∃ ν : ℝ, 1 < ν ∧
    ∃ K : ℝ, 0 < K ∧ ∀ margin : ℝ, 0 < margin →
    ∃ radius > 0, ∃ η > 0, ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∃ C Cinv : ℝ, 0 ≤ C ∧ 0 ≤ Cinv ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ N : ℕ,
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
        (∀ k z, ‖fderiv ℝ (H k) z - (system.euclideanDiagonal (U k) (S k)).toContinuousLinearMap‖ < margin) ∧
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
        (∀ z, ‖fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N) z‖ ≤ K^N) ∧
        (∀ z, ‖fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N).symm z‖ ≤ K^N) ∧
        (∀ z w, ‖fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N) z-
            fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N) w‖ ≤
          GlobalHomeomorphWordHolderBounds.holderConstant K (max C Cinv) α N*‖z-w‖^α) ∧
        (∀ z w, ‖fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N).symm z-
            fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N).symm w‖ ≤
          GlobalHomeomorphWordHolderBounds.holderConstant K (max C Cinv) α N*‖z-w‖^α) ∧
        (0 < N → ∀ z : system.EuclideanModel,
          let D := fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N) z
          (∀ ξ, D.adjoint ξ ∉ ProjectionConeTransversality.cone system.euclideanSecondProjection
              (OneStepConePolarization.narrowOpening system.rate) →
            ‖D.adjoint ξ‖ ≤ 10*μ^N*‖ξ‖) ∧
          (∀ ξ, ξ ∉ interior (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2)) →
            (4*(ν⁻¹)^N)⁻¹*‖ξ‖ ≤ ‖D.adjoint ξ‖) ∧
          ∀ ξ, ξ ≠ 0 → ξ ∉ interior (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2)) →
            D.adjoint ξ ∈ ProjectionConeTransversality.cone system.euclideanSecondProjection
              (OneStepConePolarization.narrowOpening system.rate) ∧
            D.adjoint ξ ∈ interior (ProjectionConeTransversality.cone system.euclideanSecondProjection
              (OneStepConePolarization.minusOpening system.rate))) := by
  obtain ⟨δ,positiveδ,stableRate,unstableRate,radial⟩ :=
    GlobalWordQuarterPhaseGeometry.exists_uniform_bounds system.rate_pos system.rate_lt_one system.euclideanDimension
  obtain ⟨quarterLe,_,_,narrowLtMinus,_,_,positiveTol,_⟩ :=
    OneStepConePolarization.opening_bounds system.rate_pos system.rate_lt_one
  obtain ⟨_μ,_positiveμ,_contractingμ,_ν,_expandingν,K,positiveK,families⟩ :=
    F.adapted_retained_half_word_geometry positiveα subunitα lower regularT backward atlas positiveStable
  refine ⟨system.rate+2*δ,by linarith [system.rate_pos],stableRate,
    1/system.rate-2*δ,unstableRate,K,positiveK,?_⟩
  intro margin positiveMargin
  obtain ⟨radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,C,Cinv,nonnegativeC,nonnegativeCinv,family⟩ :=
    families (min margin (min δ (ProjectionConeRateMargin.tolerance system.rate)))
      (lt_min positiveMargin (lt_min positiveδ positiveTol))
  refine ⟨radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,C,Cinv,nonnegativeC,nonnegativeCinv,?_⟩
  intro ε hp hw N control c d hc hd x y hx hy near
  obtain ⟨H,U,S,stable,unstable,inverseBound,close,properties,fake,_oldRadial⟩ :=
    family ε hp hw N control c d hc hd x y hx hy near
  have regularity : 1 ≤ r := by linarith
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using regularity)
  have smooth (k : Fin N) : ContDiff ℝ 1 (H k) :=
    (properties k).2.1.differentiable.contDiff.of_le (by exact_mod_cast order)
  have inverseSmooth (k : Fin N) : ContDiff ℝ 1 (H k).symm :=
    (properties k).2.2.1.differentiable.contDiff.of_le (by exact_mod_cast order)
  have commonNonnegative : 0 ≤ max C Cinv := le_trans nonnegativeC (le_max_left _ _)
  have wordBounds := GlobalHomeomorphWordHolderBounds.prefix_bounds H smooth inverseSmooth positiveK.le
    commonNonnegative positiveα.le
    (fun k => (properties k).2.2.2.1) (fun k => (properties k).2.2.2.2.1)
    (fun k z w => ((properties k).2.2.2.2.2.1 z w).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)))
    (fun k z w => ((properties k).2.2.2.2.2.2 z w).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)))
    (fun k : Fin N => k) N le_rfl
  refine ⟨H,U,S,stable,unstable,inverseBound,?_,properties,fake,
    wordBounds.1,wordBounds.2.1,wordBounds.2.2.1,wordBounds.2.2.2,?_⟩
  · intro k z
    exact (close k z).trans_le (min_le_left _ _)
  · intro positiveN z
    have smoothD : ∀ k : Fin N, Differentiable ℝ (H k) := fun k => (smooth k).differentiable one_ne_zero
    have inverseD : ∀ k : Fin N, Differentiable ℝ (H k).symm :=
      fun k => (inverseSmooth k).differentiable one_ne_zero
    have radialBounds := radial H smoothD inverseD U (fun k => (S k).toContinuousLinearMap)
      stable unstable (fun k w => (close k w).le.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (fun k : Fin N => k) z
    refine ⟨fun ξ hξ => radialBounds.1 ξ (fun h => hξ (OneStepConePolarization.cone_mono _ quarterLe h)),
      radialBounds.2, ?_⟩
    intro ξ nonzero outside
    have polar := GlobalWordOneStepPolarization.global_word_polarization system.euclideanDimension
      system.rate_pos system.rate_lt_one H smoothD inverseD U S stable unstable
      (fun k w => (close k w).le.trans ((min_le_right _ _).trans (min_le_right _ _)))
      positiveN (fun k : Fin N => k) z ξ nonzero outside
    exact ⟨interior_subset polar.2,
      ProjectionConeRadialMargin.nonzero_mem_interior _ narrowLtMinus (interior_subset polar.2) polar.1⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
