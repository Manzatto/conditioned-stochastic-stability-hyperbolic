module

public import LeanShared.Geometry.SmoothSupportedManifoldCore

/-! Literal smooth-test multiplication preserves the actual supported
manifold core. Only its ordinary and anisotropic norm bounds remain classical. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.SmoothSupportedManifoldCore

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] (V : Set M)

def multiplier (h : M → ℂ)
    (hh : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ h) : core (E := E) V →ₗ[ℂ] core (E := E) V where
  toFun f := ⟨(fun x => f.val x * h x), by
    constructor
    · have hm : ContMDiff (𝓘(ℝ, ℂ × ℂ)) (𝓘(ℝ, ℂ)) ∞
          (fun p : ℂ × ℂ => p.1 * p.2) :=
        (contDiff_mul : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2)).contMDiff
      exact hm.comp (f.property.1.prodMk_space hh)
    · exact (tsupport_mul_subset_left (f := f.val) (g := h)).trans f.property.2⟩
  map_add' f g := Subtype.ext (funext fun x => add_mul (f.val x) (g.val x) (h x))
  map_smul' c f := Subtype.ext (funext fun x => mul_assoc c (f.val x) (h x))


@[simp] theorem multiplier_apply (h : M → ℂ)
    (hh : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ h) (f : core (E := E) V) (x : M) :
    functions V (multiplier V h hh f) x = functions V f x * h x := rfl

end LeanShared.SmoothSupportedManifoldCore
