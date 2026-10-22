module
public import LeanShared.Geometry.CompactCoherentCenteredCharts
public import Mathlib.Tactic.Abel

/-! A single actual chart is selected at each point of the constructed
finite cover. Normalized coordinates and decoding use that same selection
at every incoming and outgoing orbit step. -/
public noncomputable section
namespace LeanShared.CoherentCenteredCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

variable {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {H : M → M} {K : Set M} {B δ : ℝ}
  (d : CompactCoherentCenteredCharts.Data (E := E) (P := P) (Q := P) H K B δ)

theorem exists_index (x : K) : ∃ i : K, i ∈ d.centers ∧ x.val ∈ interior (d.patch i) := by
  obtain ⟨i, member⟩ := mem_iUnion.mp (d.cover x.property)
  obtain ⟨hi, hx⟩ := mem_iUnion.mp member
  exact ⟨i, hi, hx⟩

@[expose] def index (x : K) : K := Classical.choose (exists_index d x)

theorem index_spec (x : K) : index d x ∈ d.centers ∧ x.val ∈ interior (d.patch (index d x)) :=
  Classical.choose_spec (exists_index d x)

@[expose] def chart (x : K) : OpenPartialHomeomorph M E := chartAt E (index d x).val

theorem chart_mem (x : K) : chart d x ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M :=
  chart_mem_maximalAtlas (index d x).val

theorem inside (x : K) : x.val ∈ (chart d x).source :=
  d.source (index d x) (interior_subset (index_spec d x).2)

@[expose] def linear (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) :
    P ≃L[ℝ] E :=
  ((frame x).trans ((CompactRiemannianChartBounds.chart_differentiable
    (chart d x) (chart_mem d x)).mfderiv (inside d x))).trans
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chart d x) x.val))

@[expose] def coordinate
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) (y : M) : P :=
  (linear d frame x).symm ((chart d x) y - (chart d x) x.val)

@[expose] def decode
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) (z : P) : M :=
  (chart d x).symm ((chart d x) x.val + linear d frame x z)

theorem coordinate_self
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) :
    coordinate d frame x x.val = 0 := by
  change (linear d frame x).symm ((chart d x) x.val - (chart d x) x.val) = 0
  rw [sub_self, map_zero]

theorem decode_zero
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) :
    decode d frame x 0 = x.val := by
  change (chart d x).symm ((chart d x) x.val + linear d frame x 0) = x.val
  rw [map_zero, add_zero, (chart d x).left_inv (inside d x)]

theorem decode_coordinate
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) (y : M)
    (member : y ∈ (chart d x).source) : decode d frame x (coordinate d frame x y) = y := by
  change (chart d x).symm ((chart d x) x.val + linear d frame x
    ((linear d frame x).symm ((chart d x) y - (chart d x) x.val))) = y
  rw [(linear d frame x).apply_symm_apply]
  have cancel : (chart d x) x.val + ((chart d x) y - (chart d x) x.val) = (chart d x) y := by abel
  rw [cancel, (chart d x).left_inv member]

theorem coordinate_decode
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val) (x : K) (z : P)
    (member : (chart d x) x.val + linear d frame x z ∈ (chart d x).target) :
    coordinate d frame x (decode d frame x z) = z := by
  change (linear d frame x).symm ((chart d x)
    ((chart d x).symm ((chart d x) x.val + linear d frame x z)) - (chart d x) x.val) = z
  rw [(chart d x).right_inv member]
  have cancel : ((chart d x) x.val + linear d frame x z) - (chart d x) x.val = linear d frame x z := by abel
  rw [cancel, (linear d frame x).symm_apply_apply]

end LeanShared.CoherentCenteredCoordinateMaps
