module
public import LeanShared.Dynamics.HyperbolicPseudoReferenceGeometry
public import LeanShared.Geometry.CoherentCenteredChartEquivalence
public import Mathlib.Tactic.Abel

/-! Actual coherent normalized charts for the constructed pseudo-reference
geometry. The same selected chart is used on incoming and outgoing steps. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

variable {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ}
  (d : HyperbolicBasicSet.PseudoReferenceGeometry h)

@[expose] def chart (x : Λ) : OpenPartialHomeomorph M E := chartAt E (d.index x).val

theorem chart_mem (x : Λ) : chart d x ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M :=
  chart_mem_maximalAtlas (d.index x).val

theorem inside (x : Λ) : x.val ∈ (chart d x).source :=
  d.chart_source (d.index x) (d.index_mem x) x (d.selected_patch x)

@[expose] def linear (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) :
    P ≃L[ℝ] E :=
  ((frame x).trans ((CompactRiemannianChartBounds.chart_differentiable
    (chart d x) (chart_mem d x)).mfderiv (inside d x))).trans
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chart d x) x.val))

@[expose] def coordinate
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) (y : M) : P :=
  (linear d frame x).symm ((chart d x) y - (chart d x) x.val)

@[expose] def decode
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) (z : P) : M :=
  (chart d x).symm ((chart d x) x.val + linear d frame x z)

theorem coordinate_self
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) :
    coordinate d frame x x.val = 0 := by
  change (linear d frame x).symm ((chart d x) x.val - (chart d x) x.val) = 0
  rw [sub_self, map_zero]

theorem decode_zero
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) :
    decode d frame x 0 = x.val := by
  change (chart d x).symm ((chart d x) x.val + linear d frame x 0) = x.val
  rw [map_zero, add_zero, (chart d x).left_inv (inside d x)]

theorem decode_coordinate
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) (y : M)
    (member : y ∈ (chart d x).source) : decode d frame x (coordinate d frame x y) = y := by
  change (chart d x).symm ((chart d x) x.val + linear d frame x
    ((linear d frame x).symm ((chart d x) y - (chart d x) x.val))) = y
  rw [(linear d frame x).apply_symm_apply]
  have cancel : (chart d x) x.val + ((chart d x) y - (chart d x) x.val) = (chart d x) y := by abel
  rw [cancel, (chart d x).left_inv member]

theorem coordinate_decode
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) (z : P)
    (member : (chart d x) x.val + linear d frame x z ∈ (chart d x).target) :
    coordinate d frame x (decode d frame x z) = z := by
  change (linear d frame x).symm ((chart d x)
    ((chart d x).symm ((chart d x) x.val + linear d frame x z)) - (chart d x) x.val) = z
  rw [(chart d x).right_inv member]
  have cancel : ((chart d x) x.val + linear d frame x z) - (chart d x) x.val = linear d frame x z := by abel
  rw [cancel, (linear d frame x).symm_apply_apply]

@[expose] def normalizedChart
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) :
    OpenPartialHomeomorph M P :=
  (chart d x).transHomeomorph
    (CoherentCenteredCoordinateMaps.affineNormalize (linear d frame x) ((chart d x) x.val))

theorem normalizedChart_apply
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) (y : M) :
    normalizedChart d frame x y = coordinate d frame x y := rfl

theorem normalizedChart_symm_apply
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) (z : P) :
    (normalizedChart d frame x).symm z = decode d frame x z := rfl

theorem normalizedChart_source
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : Λ) :
    (normalizedChart d frame x).source = (chart d x).source := rfl

end LeanShared.PseudoReferenceCoordinateMaps
