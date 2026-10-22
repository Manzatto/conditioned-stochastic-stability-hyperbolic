module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedJointHolderGlobalExtensions
public import LeanShared.Analysis.GlobalWordAdjointRadialBounds
public import LeanShared.Analysis.OrthogonalHalfConeGlobalWordFakeLeaves
public import LeanShared.Analysis.OrthogonalRateGlobalWordFakeLeaves
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones

/-! One actual global family simultaneously has the literal adapted
extension formula, common two-sided Holder derivative bounds, and strict
forward/inverse-adjoint cone actions at the original hyperbolic rate. -/
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

theorem Maps.adapted_retained_half_word_geometry {r α : ℝ}
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
        ∀ z : system.EuclideanModel,
          let D := fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun k => k) N) z
          (∀ β : ℝ, 1/2 ≤ β → ∀ ξ,
            D.adjoint ξ ∉ ProjectionConeTransversality.cone system.euclideanSecondProjection β →
              ‖D.adjoint ξ‖ ≤ 4*μ^N*‖ξ‖) ∧
          (∀ ξ, ξ ∉ interior (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2)) →
            (4*(ν⁻¹)^N)⁻¹*‖ξ‖ ≤ ‖D.adjoint ξ‖) ∧
          (∀ β : ℝ, 1/2 ≤ β → ∀ ξ,
            D.adjoint ξ ∈ ProjectionConeTransversality.cone system.euclideanSecondProjection β ∨
              ‖D.adjoint ξ‖ ≤ 4*μ^N*‖ξ‖) := by
  obtain ⟨δ,positiveδ,stableRate,unstableRate,radial⟩ :=
    GlobalWordAdjointRadialBounds.exists_uniform_bounds system.rate_pos system.rate_lt_one system.euclideanDimension
  obtain ⟨K,positiveK,extensions⟩ :=
    F.adapted_joint_holder_global_euclidean_extensions positiveα subunitα lower regularT backward atlas
  refine ⟨system.rate+2*δ,by linarith [system.rate_pos],stableRate,1/system.rate-2*δ,unstableRate,
    2*K+δ,by positivity,?_⟩
  intro margin positiveMargin
  obtain ⟨radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,ρ,
    smoothρ,compactρ,supportρ,oneρ,C,Cinv,nonnegativeC,nonnegativeCinv,extension⟩ := extensions (min δ margin) (lt_min positiveδ positiveMargin)
  have marginBound : min δ margin ≤ δ := min_le_left δ margin
  refine ⟨radius,positiveRadius,η,positiveη,cutoff,positiveCutoff,cap,
    C,Cinv,nonnegativeC,nonnegativeCinv,?_⟩
  intro ε hp hw N control c d hc hd x y hx hy near
  have data (k : Fin N) := extension (c k) (hc k) (d k) (hd k) (x k) (hx k) (y k) (hy k) (near k)
  choose S U boundS boundU boundA boundInv family using data
  choose O openO contains J formula joint jointInv legal using (fun k => family k ε hp hw)
  let H (k : Fin N) := J k (control k).val
  have properties (k : Fin N) := legal k (control k)
  refine ⟨H,U,S,boundS,boundU,?_,?_,?_,?_,?_⟩
  · intro k
    exact (boundInv k).trans (by linarith)
  · intro k z
    exact ((properties k).2.2.1 z).trans_le (min_le_right δ margin)
  · intro k
    obtain ⟨regularH,regularInv,derivative,inside,outside,forwardBound,inverseBound,holder,inverseHolder,
      coneDerivative,forwardCone,inverseCone⟩ := properties k
    exact ⟨inside,regularH,regularInv,fun z => (forwardBound z).trans (by linarith),
      fun z => (inverseBound z).trans (by linarith),holder,inverseHolder⟩
  · intro Γ fake n
    have regularity : 1 ≤ r := by linarith
    have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using regularity)
    have smooth (k : Fin N) : Differentiable ℝ (H k) :=
      (properties k).1.differentiable.contDiff.differentiable (by exact_mod_cast (Nat.ne_of_gt order))
    have close (k : Fin N) (w : system.EuclideanModel) :
        ‖fderiv ℝ (H k) w-(system.euclideanDiagonal (U k) (S k)).toContinuousLinearMap‖ ≤
          OrthogonalDiagonalRatePerturbation.radius system.rate K := by
      obtain ⟨_,_,_,_,_,_,_,_,_,coneDerivative,_,_⟩ := properties k
      exact (coneDerivative w).le
    have result := OrthogonalHalfConeGlobalWordFakeLeaves.whole_word_image_zero system.euclideanDimension
      (by simpa only [finrank_euclideanSpace,Fintype.card_fin] using positiveStable)
      system.rate K system.rate_pos system.rate_lt_one positiveK.le U S boundS boundU boundInv H smooth close
      (Γ := Γ) (by simpa only [PatchSystem.euclideanFirstProjection,finrank_euclideanSpace,
        Fintype.card_fin] using fake) (fun k : Fin N => k) n
    simpa only [PatchSystem.euclideanFirstProjection,finrank_euclideanSpace,Fintype.card_fin] using result
  · intro z
    have regularity : 1 ≤ r := by linarith
    have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using regularity)
    have smooth (k : Fin N) : Differentiable ℝ (H k) :=
      (properties k).1.differentiable.contDiff.differentiable (by exact_mod_cast (Nat.ne_of_gt order))
    have inverseSmooth (k : Fin N) : Differentiable ℝ (H k).symm :=
      (properties k).2.1.differentiable.contDiff.differentiable (by exact_mod_cast (Nat.ne_of_gt order))
    have close (k : Fin N) (w : system.EuclideanModel) :
        ‖fderiv ℝ (H k) w-OrthogonalProductCoordinates.transport system.euclideanDimension
          ((U k).toContinuousLinearMap.prodMap (S k).toContinuousLinearMap)‖ ≤ δ := by
      exact ((properties k).2.2.1 w).le.trans (min_le_left δ margin)
    exact radial H smooth inverseSmooth U (fun k => (S k).toContinuousLinearMap) boundS boundU close
      (fun k : Fin N => k) z

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
