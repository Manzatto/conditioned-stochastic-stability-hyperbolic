module
public import LeanShared.Dynamics.HyperbolicAdaptedChartPatches
public import LeanShared.Dynamics.HyperbolicAdaptedWholeFrameContinuity
public import LeanShared.Geometry.CompactCenteredFrameComparison

/-! Nearby references in each actual adapted patch use uniformly close
relative normalizations in the same fixed ordinary chart. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet HyperbolicAdaptedFramePatches
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

@[expose] def PatchSystem.frameDomain (system : PatchSystem b) (center : Λ) : Set Λ :=
  Subtype.val ⁻¹' (((system.unstableFrame center).neighborhood ∩
    (system.stableFrame center).neighborhood) ∩ (chartAt E center.val).source)

theorem PatchSystem.frameDomain_open (system : PatchSystem b) (center : Λ) :
    IsOpen (system.frameDomain center) :=
  (((system.unstableFrame center).open_neighborhood.inter
    (system.stableFrame center).open_neighborhood).inter
      (chartAt E center.val).open_source).preimage continuous_subtype_val

@[expose] def PatchSystem.referenceFrame (system : PatchSystem b) (center : Λ)
    (y : system.frameDomain center) :
    (EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension)) ≃L[ℝ]
        TangentSpace (𝓘(ℝ, E)) y.val.val :=
  wholeFrame (system.unstableFrame center) (system.stableFrame center)
    ⟨y.val.val, y.val.property, y.property.1⟩

theorem PatchSystem.referenceFrame_sections (system : PatchSystem b) (center : Λ)
    (v : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension)) :
    Continuous (fun y : system.frameDomain center =>
      (⟨y.val.val, system.referenceFrame center y v⟩ : TangentBundle (𝓘(ℝ, E)) M)) := by
  let inclusion : system.frameDomain center →
      ↥(Λ ∩ ((system.unstableFrame center).neighborhood ∩
        (system.stableFrame center).neighborhood)) :=
    fun y => ⟨y.val.val, y.val.property, y.property.1⟩
  have continuousInclusion : Continuous inclusion :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact (wholeFrame_joint (system.unstableFrame center) (system.stableFrame center)).comp
    (continuousInclusion.prodMk continuous_const)

theorem PatchSystem.relative_reference_radius (system : PatchSystem b) (center : Λ)
    (K : Set Λ) (compact : IsCompact K) (inside : K ⊆ system.frameDomain center)
    (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ η > 0, ∀ x (hx : x ∈ K), ∀ y, dist x y < η → ∃ hy : y ∈ system.frameDomain center,
      ‖(ContinuousCenteredFrameCharts.chartFrame center.val x.val (inside hx).2
          (system.referenceFrame center ⟨x, inside hx⟩)).symm.toContinuousLinearMap.comp
        (ContinuousCenteredFrameCharts.chartFrame center.val y.val hy.2
          (system.referenceFrame center ⟨y, hy⟩)).toContinuousLinearMap -
            ContinuousLinearMap.id ℝ _‖ < δ := by
  exact CompactCenteredFrameComparison.exists_radius (system.frameDomain center) K
    (system.frameDomain_open center) compact inside center.val Subtype.val
    (fun y => y.property.2) (system.referenceFrame center)
    (system.referenceFrame_sections center) δ positiveδ

end LeanShared.HyperbolicAdaptedPatchSystem
