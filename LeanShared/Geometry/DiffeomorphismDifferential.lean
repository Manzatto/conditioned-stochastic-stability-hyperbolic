module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import LeanShared.Geometry.FractionalManifoldRegularity

/-! The intrinsic differential used by principal coefficients is constructed
from the actual differentiable diffeomorphism and its differentiable inverse. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.DiffeomorphismDifferential
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (T : M ≃ₜ M)
  (hT : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
  (hi : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)

def differential (x : M) :
    TangentSpace (𝓘(ℝ, E)) x ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (T x) := by
  let h : T.toOpenPartialHomeomorph.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) :=
    ⟨fun x _ => (hT x).mdifferentiableWithinAt,
      fun x _ => (hi x).mdifferentiableWithinAt⟩
  exact h.mfderiv (mem_univ x)

@[simp] theorem differential_apply (x : M) (v : TangentSpace (𝓘(ℝ, E)) x) :
    differential T hT hi x v = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v := rfl

end LeanShared.DiffeomorphismDifferential

namespace LeanShared.FractionalManifoldRegularity
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem Regular.mdifferentiable {r : ℝ} {f : M → N}
    (h : Regular (E := E) (F := F) r f) (hr : 1 ≤ r) :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) f := by
  have hn : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hr)
  exact (h.differentiable.of_le (by exact_mod_cast hn) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) 1 f).mdifferentiable one_ne_zero

end LeanShared.FractionalManifoldRegularity
