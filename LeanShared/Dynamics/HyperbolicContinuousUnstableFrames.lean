module

public import LeanShared.Dynamics.HyperbolicContinuousKernelFrames

/-! The genuine local continuous frames lie in the literal unstable
subspaces, obtained from the actual projection-kernel identity. -/
public noncomputable section
open Set Bundle IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

@[expose] def HyperbolicData.kernelUnstableEquiv (h : HyperbolicData (E := E) T Λ)
    (x : M) (hx : x ∈ Λ) : (h.projection x).ker ≃L[ℝ] h.unstable x :=
  (ContinuousLinearEquiv.refl ℝ (TangentSpace (𝓘(ℝ, E)) x)).ofSubmodules _ _
    (by
      change (h.projection x).ker.map LinearMap.id=h.unstable x
      simpa only [Submodule.map_id] using h.projection_kernel x hx)

theorem HyperbolicData.exists_continuous_unstable_frames (h : HyperbolicData (E := E) T Λ)
    (x : M) (hx : x ∈ Λ) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∃ H : ∀ y : ↥(Λ ∩ O), h.unstable x ≃L[ℝ] h.unstable y.val,
        ∀ u : h.unstable x, Continuous (fun y : ↥(Λ ∩ O) =>
          (⟨y.val,(H y u).val⟩ : TangentBundle (𝓘(ℝ, E)) M)) := by
  obtain ⟨O,openO,member,H,frames⟩ := h.exists_continuous_kernel_frames x hx
  let source := (h.kernelUnstableEquiv x hx).symm
  let target (y : ↥(Λ ∩ O)) := h.kernelUnstableEquiv y.val y.property.1
  refine ⟨O,openO,member,(fun y => source.trans ((H y).trans (target y))),?_⟩
  intro u
  exact (frames (source u)).congr (fun _ => rfl)

end LeanShared.HyperbolicBasicSet
