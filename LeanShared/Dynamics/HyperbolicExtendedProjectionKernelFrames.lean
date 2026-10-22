module
public import LeanShared.Dynamics.HyperbolicNormedAdaptedProjection
public import LeanShared.Geometry.BundleKernelFrames

/-! The constructed extended projector has genuine continuous local
kernel frames on its entire open collar, not only on the invariant core. -/
@[expose] public noncomputable section
open Set Filter Bundle IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}

theorem exists_collar_kernel_frames (a : h.NormedAdaptedProjection) (x : M) (hx : x ∈ a.collar) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∃ H : ∀ y : ↥(a.collar ∩ O), (a.projection x).ker ≃L[ℝ] (a.projection y.val).ker,
        ∀ u : (a.projection x).ker, Continuous (fun y : ↥(a.collar ∩ O) =>
          (⟨y.val,(H y u).val⟩ : TangentBundle (𝓘(ℝ,E)) M)) := by
  let fibers : M → Type _ := TangentSpace (𝓘(ℝ,E))
  let e := trivializationAt E fibers x
  have base : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let P := BundleEndomorphismCoordinates.coordinates fibers e a.projection
  have contP : ContinuousWithinAt P (a.collar ∩ e.baseSet) x :=
    BundleEndomorphismCoordinates.continuousOn_coordinates fibers e a.projection a.collar
      a.continuous_action x ⟨hx,base⟩
  have centered : ‖P x-P x‖*(2*‖P x‖+1)<1 := by simp
  have near : ∀ᶠ y in 𝓝[a.collar ∩ e.baseSet] x, ‖P x-P y‖*(2*‖P x‖+1)<1 :=
    ((continuousWithinAt_const.sub contP).norm.mul continuousWithinAt_const).eventually
      (gt_mem_nhds centered)
  obtain ⟨V,neighborhood,bound⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp near
  obtain ⟨W,contained,openW,member⟩ := mem_nhds_iff.mp neighborhood
  let O := W ∩ e.baseSet
  have inside : a.collar ∩ O ⊆ e.baseSet := fun _ hy => hy.2.2
  have idem : ∀ y ∈ insert x (a.collar ∩ O), ∀ v,
      a.projection y (a.projection y v)=a.projection y v := by
    intro y hy v
    have live : y ∈ a.collar := by
      rcases hy with rfl | hy
      · exact hx
      · exact hy.1
    exact congrArg (fun A : fibers y →L[ℝ] fibers y => A v) (a.idempotent y live).eq
  have small : ∀ y ∈ a.collar ∩ O, ‖P x-P y‖*(2*‖P x‖+1)<1 := by
    intro y hy
    exact bound ⟨contained hy.2.1,hy.1,hy.2.2⟩
  refine ⟨O,openW.inter e.open_baseSet,⟨member,base⟩,
    BundleKernelFrames.frame fibers e a.projection (a.collar ∩ O) x base inside idem small,?_⟩
  intro u
  apply BundleKernelFrames.continuous_frame
  exact a.continuous_action.mono (fun _ hv => hv.1)

end LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
