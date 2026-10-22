module
public import LeanShared.Dynamics.HyperbolicAdaptedPatchSystem
public import LeanShared.Geometry.SmoothCenteredFrameCharts

/-! Refine the already constructed adapted-frame patches into fixed ordinary
chart sources, preserving the frame families, adapted time and bounds. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

omit [FiniteDimensional ℝ E]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
theorem PatchSystem.exists_chart_cover (system : PatchSystem b) :
    ∃ centers : Finset Λ, ∃ patch : Λ → Set Λ,
      (∀ x, IsCompact (patch x) ∧ patch x ⊆ system.patch x ∧
        (∀ y ∈ patch x, y.val ∈ (chartAt E x.val).source) ∧ x ∈ interior (patch x)) ∧
      (univ : Set Λ) ⊆ ⋃ x ∈ centers, interior (patch x) := by
  classical
  let U : Λ → Set Λ := fun x => interior (system.patch x) ∩
    Subtype.val ⁻¹' (chartAt E x.val).source
  have openU (x : Λ) : IsOpen (U x) := isOpen_interior.inter
    ((chartAt E x.val).open_source.preimage continuous_subtype_val)
  have memberU (x : Λ) : x ∈ U x :=
    ⟨(system.patch_properties x).2.2, mem_chart_source E x.val⟩
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  obtain ⟨centers, patch, properties, covers⟩ := FiniteCompactNeighborhoodCover.exists_cover
    (univ : Set Λ) isCompact_univ U openU (fun x _ => memberU x)
  refine ⟨centers.image Subtype.val, (fun x => patch ⟨x, mem_univ x⟩), ?_, ?_⟩
  · intro x
    have facts := properties ⟨x, mem_univ x⟩
    refine ⟨facts.1, ?_, ?_, facts.2.2⟩
    · intro y hy
      exact interior_subset (facts.2.1 hy).1
    · intro y hy
      exact (facts.2.1 hy).2
  · intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp (covers hy)
    obtain ⟨hx, member⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨x.val, mem_iUnion.mpr
      ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, member⟩⟩

end LeanShared.HyperbolicAdaptedPatchSystem
