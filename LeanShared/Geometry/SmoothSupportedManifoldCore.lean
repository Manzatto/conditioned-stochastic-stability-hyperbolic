module

public import LeanShared.Geometry.ChartLocalization
public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# The actual smooth compactly supported manifold core

On a compact ambient manifold, smooth functions whose topological support
is contained in the prescribed open live region are precisely the concrete
common core needed by the manifold anisotropic norm constructors. Its
function representation is injective; smoothness and support are proved
from subtype membership, not assumptions on an abstract core map.
-/

@[expose] public noncomputable section

open Set IsManifold
open scoped Manifold ContDiff

namespace LeanShared.SmoothSupportedManifoldCore

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] (V : Set M)

/-- The literal smooth supported functions, as a complex linear submodule. -/
def core : Submodule ℂ (M → ℂ) where
  carrier := {f | ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ f ∧ tsupport f ⊆ V}
  zero_mem' := ⟨contMDiff_const, by simp only [tsupport_zero, empty_subset]⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, (tsupport_add _ _).trans (union_subset hf.2 hg.2)⟩
  smul_mem' c f hf := ⟨by
    let T : ℂ →L[ℝ] ℂ := c • ContinuousLinearMap.id ℝ ℂ
    exact T.contMDiff.comp hf.1,
    (tsupport_smul_subset_right (fun _ : M => c) f).trans hf.2⟩

/-- Actual function representation of the concrete manifold core. -/
def functions : core (E := E) V →ₗ[ℂ] (M → ℂ) := (core (E := E) V).subtype

theorem functions_injective : Function.Injective (functions (E := E) V) := Subtype.val_injective

theorem smooth (f : core (E := E) V) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions V f) := f.property.1

theorem support (f : core (E := E) V) : tsupport (functions V f) ⊆ V := f.property.2

theorem zero_outside (f : core (E := E) V) (x : M) (hx : x ∉ V) : functions V f x = 0 := by
  by_contra hn
  exact hx (support V f (subset_tsupport (functions V f) hn))

/-- Compact ambient manifolds give genuine compact support automatically. -/
theorem compact_support [CompactSpace M] (f : core (E := E) V) :
    HasCompactSupport (functions V f) := HasCompactSupport.of_compactSpace _

end LeanShared.SmoothSupportedManifoldCore
