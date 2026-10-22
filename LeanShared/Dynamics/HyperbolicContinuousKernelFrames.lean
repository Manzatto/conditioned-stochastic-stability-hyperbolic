module

public import LeanShared.Dynamics.HyperbolicProjectionCoordinates
public import LeanShared.Geometry.BundleKernelFrames

/-! Actual continuous local unstable frames are constructed from the
continuous hyperbolic projection and a genuine tangent-bundle chart. -/
public noncomputable section
open Set Filter Bundle IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem HyperbolicData.exists_continuous_kernel_frames (h : HyperbolicData (E := E) T Λ)
    (x : M) (hx : x ∈ Λ) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∃ H : ∀ y : ↥(Λ ∩ O), (h.projection x).ker ≃L[ℝ] (h.projection y.val).ker,
        ∀ u : (h.projection x).ker, Continuous (fun y : ↥(Λ ∩ O) =>
          (⟨y.val,(H y u).val⟩ : TangentBundle (𝓘(ℝ, E)) M)) := by
  let fibers : M → Type _ := TangentSpace (𝓘(ℝ, E))
  let e := trivializationAt E fibers x
  have base : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let P := BundleEndomorphismCoordinates.coordinates fibers e h.projection
  have contP : ContinuousWithinAt P (Λ ∩ e.baseSet) x :=
    h.projection_coordinates_continuous e x ⟨hx,base⟩
  have centered : ‖P x-P x‖*(2*‖P x‖+1)<1 := by simp
  have near : ∀ᶠ y in 𝓝[Λ ∩ e.baseSet] x, ‖P x-P y‖*(2*‖P x‖+1)<1 :=
    ((continuousWithinAt_const.sub contP).norm.mul continuousWithinAt_const).eventually
      (gt_mem_nhds centered)
  obtain ⟨V,neighborhood,bound⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp near
  obtain ⟨W,contained,openW,member⟩ := mem_nhds_iff.mp neighborhood
  let O := W ∩ e.baseSet
  have inside : Λ ∩ O ⊆ e.baseSet := fun _ hy => hy.2.2
  have idem : ∀ y ∈ insert x (Λ ∩ O), ∀ v, h.projection y (h.projection y v)=h.projection y v := by
    intro y hy v
    have live : y ∈ Λ := by
      rcases hy with rfl | hy
      · exact hx
      · exact hy.1
    exact congrArg (fun A : fibers y →L[ℝ] fibers y => A v) (h.projection_idempotent y live)
  have small : ∀ y ∈ Λ ∩ O, ‖P x-P y‖*(2*‖P x‖+1)<1 := by
    intro y hy
    exact bound ⟨contained hy.2.1,hy.1,hy.2.2⟩
  refine ⟨O,openW.inter e.open_baseSet,⟨member,base⟩,
    BundleKernelFrames.frame fibers e h.projection (Λ ∩ O) x base inside idem small,?_⟩
  intro u
  apply BundleKernelFrames.continuous_frame
  exact h.continuous_splitting.mono (fun v hv => hv.1)

end LeanShared.HyperbolicBasicSet
