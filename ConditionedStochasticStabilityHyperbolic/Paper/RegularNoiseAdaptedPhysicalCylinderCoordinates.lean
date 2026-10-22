module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedExtensionWordEventualAgreement
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedExtensionWordAgreement
public import LeanShared.Dynamics.HyperbolicAdaptedGlobalProjection
public import LeanShared.Geometry.NormalizedChartCoordinateIdentity
public import LeanShared.Analysis.OrthogonalRateGlobalWordFakeLeaves
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones

/-! Exact physical-cylinder coordinates. Chart cancellation gives the native
image identity, and open prefix tracking gives the actual local germ of the
whole global extension. Neither conclusion is a separate geometric input. -/
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
theorem Maps.adapted_physical_cylinder_coordinates {r : ℝ}
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
      let physical := CylinderPrincipalCoefficient.prefixOrbit
        (fun j : Fin N => F.family ε (control j).val) (fun j => j) N
      let W := OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H (fun j => j) N
      let L := ContinuousCenteredFrameCharts.chartFrame (c 0).val (p 0).val
        (atlas.inside (c 0) (inside 0)).2
        (system.euclideanReferenceFrame (c 0) ⟨p 0, atlas.inside (c 0) (inside 0)⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame (c N).val (p N).val
        (atlas.inside (c N) (inside N)).2
        (system.euclideanReferenceFrame (c N) ⟨p N, atlas.inside (c N) (inside N)⟩)
      physical (system.normalizedProjectionPoint (c 0)
          ⟨p 0, atlas.inside (c 0) (inside 0)⟩ (κ 0 m)) =
        system.normalizedProjectionPoint (c N)
          ⟨p N, atlas.inside (c N) (inside N)⟩ (W (κ 0 m)) ∧
      (W : system.EuclideanModel → system.EuclideanModel) =ᶠ[𝓝 (κ 0 m)]
        centered L R ((chartAt E (c 0).val) (p 0).val)
          ((chartAt E (c N).val) (p N).val)
          (chartAt E (c N).val ∘ physical ∘ (chartAt E (c 0).val).symm) := by
  dsimp only
  intro H agreement m valid tracking
  let κ := fun k => ContinuousCenteredFrameCharts.normalizedChart (c k).val (p k).val
    (atlas.inside (c k) (inside k)).2
    (system.euclideanReferenceFrame (c k) ⟨p k, atlas.inside (c k) (inside k)⟩)
  let physical := CylinderPrincipalCoefficient.prefixOrbit
    (fun j : Fin N => F.family ε (control j).val) (fun j => j) N
  have decode0 : system.normalizedProjectionPoint (c 0)
      ⟨p 0, atlas.inside (c 0) (inside 0)⟩ (κ 0 m) = m := by
    change (κ 0).symm (κ 0 m) = m
    exact (κ 0).left_inv (valid 0 (Nat.zero_le N))
  have decodeN : system.normalizedProjectionPoint (c N)
      ⟨p N, atlas.inside (c N) (inside N)⟩ (κ N (physical m)) = physical m := by
    change (κ N).symm (κ N (physical m)) = physical m
    exact (κ N).left_inv (valid N le_rfl)
  have wordEq := F.adapted_extension_word_eq atlas ε control c p inside radius H agreement m
    valid (fun k hk => mem_closedBall.mpr (mem_ball.mp (tracking k hk)).le) N le_rfl
  constructor
  · change physical (system.normalizedProjectionPoint (c 0)
        ⟨p 0, atlas.inside (c 0) (inside 0)⟩ (κ 0 m)) = _
    rw [decode0, wordEq, decodeN]
  · have germ := F.adapted_extension_word_eventuallyEq atlas ε positive window control c p
      inside radius H agreement m valid tracking
    have exactCoordinate := ContinuousCenteredFrameCharts.normalized_coordinate_eq
      (c 0).val (c N).val (p 0).val (p N).val
      (atlas.inside (c 0) (inside 0)).2 (atlas.inside (c N) (inside N)).2
      (system.euclideanReferenceFrame (c 0) ⟨p 0, atlas.inside (c 0) (inside 0)⟩)
      (system.euclideanReferenceFrame (c N) ⟨p N, atlas.inside (c N) (inside N)⟩)
      physical
    exact germ.trans (Filter.Eventually.of_forall (fun z => congrFun exactCoordinate z))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
