module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedPhysicalCylinderCoordinates

/-! The actual physical-cylinder image and germ, expressed at an arbitrary
normalized source point. Target membership supplies the genuine chart right
inverse; all remaining hypotheses describe the literal tracked cylinder. -/
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
theorem Maps.adapted_physical_cylinder_source_coordinates {r : ℝ}
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
    ∀ z ∈ (κ 0).target,
      let m := system.normalizedProjectionPoint (c 0)
        ⟨p 0, atlas.inside (c 0) (inside 0)⟩ z
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
          ⟨p 0, atlas.inside (c 0) (inside 0)⟩ z) =
        system.normalizedProjectionPoint (c N)
          ⟨p N, atlas.inside (c N) (inside N)⟩ (W z) ∧
      (W : system.EuclideanModel → system.EuclideanModel) =ᶠ[𝓝 z]
        centered L R ((chartAt E (c 0).val) (p 0).val)
          ((chartAt E (c N).val) (p N).val)
          (chartAt E (c N).val ∘ physical ∘ (chartAt E (c 0).val).symm) := by
  dsimp only
  intro H agreement z target valid tracking
  let κ := fun k => ContinuousCenteredFrameCharts.normalizedChart (c k).val (p k).val
    (atlas.inside (c k) (inside k)).2
    (system.euclideanReferenceFrame (c k) ⟨p k, atlas.inside (c k) (inside k)⟩)
  let m := system.normalizedProjectionPoint (c 0)
    ⟨p 0, atlas.inside (c 0) (inside 0)⟩ z
  have encode : κ 0 m = z := by
    change (κ 0) ((κ 0).symm z) = z
    exact (κ 0).right_inv target
  have result := F.adapted_physical_cylinder_coordinates atlas ε positive window control
    c p inside radius H agreement m valid tracking
  dsimp only [κ] at encode
  simpa only [encode] using result

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
