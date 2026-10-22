module
public import LeanShared.Geometry.CoherentCenteredCoordinateMaps
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Actual open partial homeomorphisms realizing the produced centered
coordinates and decoder. Their sources and targets are the genuine chart
sources and normalized preimages, rather than asserted coordinate laws. -/
public noncomputable section
namespace LeanShared.CoherentCenteredCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

@[expose] def affineNormalize
    {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (L : P ≃L[ℝ] E) (a : E) : E ≃ₜ P where
  toFun v := L.symm (v - a)
  invFun z := a + L z
  left_inv v := by
    change a + L (L.symm (v - a)) = v
    rw [L.apply_symm_apply]
    abel
  right_inv z := by
    change L.symm ((a + L z) - a) = z
    rw [add_sub_cancel_left, L.symm_apply_apply]
  continuous_toFun := L.symm.continuous.comp (continuous_id.sub continuous_const)
  continuous_invFun := L.continuous.const_add a

variable {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {H : M → M} {K : Set M} {B δ : ℝ}
  (d : CompactCoherentCenteredCharts.Data (E := E) (P := P) (Q := P) H K B δ)

@[expose] def normalizedChart
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) :
    OpenPartialHomeomorph M P :=
  (chart d x).transHomeomorph (affineNormalize (linear d frame x) (chart d x x.val))

theorem normalizedChart_apply
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) (y : M) :
    normalizedChart d frame x y = coordinate d frame x y := rfl

theorem normalizedChart_symm_apply
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) (z : P) :
    (normalizedChart d frame x).symm z = decode d frame x z := rfl

theorem normalizedChart_source
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) :
    (normalizedChart d frame x).source = (chart d x).source := rfl

theorem normalizedChart_target
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) (z : P) :
    z ∈ (normalizedChart d frame x).target ↔
      chart d x x.val + linear d frame x z ∈ (chart d x).target := Iff.rfl

end LeanShared.CoherentCenteredCoordinateMaps
