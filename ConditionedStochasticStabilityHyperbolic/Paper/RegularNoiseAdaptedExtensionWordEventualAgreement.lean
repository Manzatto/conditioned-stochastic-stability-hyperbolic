module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedEuclideanBlocks
public import LeanShared.Geometry.PartialChartOpenCylinder
public import LeanShared.Geometry.NormalizedChartCoordinateIdentity
public import LeanShared.Analysis.OrthogonalRateGlobalWordFakeLeaves
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones

/-! One actual global family simultaneously has the literal adapted
extension formula, common two-sided Holder derivative bounds, and strict
forward/inverse-adjoint cone actions at the original hyperbolic rate. -/
public noncomputable section
open Set Filter IsManifold Bundle Metric
open scoped Manifold ContDiff NNReal Topology
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

omit [FiniteDimensional ℝ E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem Maps.adapted_extension_word_eventuallyEq {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window) {N : ℕ} (control : Fin N → cube (ι := ι) ε)
    (c p : ℕ → Λ) (inside : ∀ k, p k ∈ atlas.patch (c k)) (radius : ℝ) :
    let κ := fun k => ContinuousCenteredFrameCharts.normalizedChart (c k).val (p k).val
      (atlas.inside (c k) (inside k)).2
      (system.euclideanReferenceFrame (c k) ⟨p k, atlas.inside (c k) (inside k)⟩)
    ∀ H : Fin N → system.EuclideanModel ≃ₜ system.EuclideanModel,
    (∀ k : Fin N,
      let L := ContinuousCenteredFrameCharts.chartFrame (c k.val).val (p k.val).val
        (atlas.inside (c k.val) (inside k.val)).2
        (system.euclideanReferenceFrame (c k.val) ⟨p k.val, atlas.inside (c k.val) (inside k.val)⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame (c (k.val+1)).val (p (k.val+1)).val
        (atlas.inside (c (k.val+1)) (inside (k.val+1))).2
        (system.euclideanReferenceFrame (c (k.val+1))
          ⟨p (k.val+1), atlas.inside (c (k.val+1)) (inside (k.val+1))⟩)
      ∀ z ∈ closedBall 0 radius,
        H k z = centered L R ((chartAt E (c k.val).val) (p k.val).val)
          ((chartAt E (c (k.val+1)).val) (p (k.val+1)).val)
          (chartAt E (c (k.val+1)).val ∘ F.family ε (control k).val ∘
            (chartAt E (c k.val).val).symm) z) →
    ∀ m : M,
      (∀ k ≤ N, CylinderPrincipalCoefficient.prefixOrbit
        (fun j : Fin N => F.family ε (control j).val) (fun j => j) k m ∈
          (chartAt E (c k).val).source) →
      (∀ k < N, κ k (CylinderPrincipalCoefficient.prefixOrbit
        (fun j : Fin N => F.family ε (control j).val) (fun j => j) k m) ∈ ball 0 radius) →
      (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun j => j) N :
        system.EuclideanModel → system.EuclideanModel) =ᶠ[𝓝 (κ 0 m)]
        (κ N ∘ CylinderPrincipalCoefficient.prefixOrbit
          (fun j : Fin N => F.family ε (control j).val) (fun j => j) N ∘ (κ 0).symm) := by
  dsimp only
  intro H agreement m valid tracking
  let κ := fun k => ContinuousCenteredFrameCharts.normalizedChart (c k).val (p k).val
    (atlas.inside (c k) (inside k)).2
    (system.euclideanReferenceFrame (c k) ⟨p k, atlas.inside (c k) (inside k)⟩)
  have actualAgreement (k : Fin N) (z : system.EuclideanModel) (hz : z ∈ closedBall 0 radius) :
      H k z = κ (k.val+1) (F.family ε (control k).val ((κ k.val).symm z)) := by
    rw [agreement k z hz]
    have exactCoordinate := ContinuousCenteredFrameCharts.normalized_coordinate_eq
      (c k.val).val (c (k.val+1)).val (p k.val).val (p (k.val+1)).val
      (atlas.inside (c k.val) (inside k.val)).2
      (atlas.inside (c (k.val+1)) (inside (k.val+1))).2
      (system.euclideanReferenceFrame (c k.val) ⟨p k.val, atlas.inside (c k.val) (inside k.val)⟩)
      (system.euclideanReferenceFrame (c (k.val+1))
        ⟨p (k.val+1), atlas.inside (c (k.val+1)) (inside (k.val+1))⟩)
      (F.family ε (control k).val)
    exact (congrFun exactCoordinate z).symm
  have continuousF (j : Fin N) : Continuous (F.family ε (control j).val) :=
    (F.map_regular ε positive window (control j)).differentiable.continuous
  have agreementOpen (k : Fin N) (z : system.EuclideanModel) (hz : z ∈ ball 0 radius) :=
    actualAgreement k z (mem_closedBall.mpr (mem_ball.mp hz).le)
  have result := PartialChartWordAgreement.eventuallyEq_endpoint
    (fun j : Fin N => F.family ε (control j).val) continuousF
    (fun j => (H j : system.EuclideanModel → system.EuclideanModel))
    κ (fun _ => ball 0 radius) (fun _ => isOpen_ball) agreementOpen m valid tracking
  rw [OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph_coe]
  exact result

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
