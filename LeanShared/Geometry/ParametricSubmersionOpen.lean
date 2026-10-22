module
public import LeanShared.Geometry.BoundarylessSubmersionOpen
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Full control rank implies openness of the actual joint endpoint map.
No inverse normal form or endpoint-image openness is assumed. -/
public section
open Set Filter IsManifold
open scoped Topology ContDiff Manifold
namespace LeanShared.SubmersionOpen

theorem endpoint_mfderiv_surjective
    {E P M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace M] [ChartedSpace E M]
    {H : M × P → M} {x : M} {a : P}
    (smooth : MDifferentiableAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, P))) (𝓘(ℝ, E)) H (x, a))
    (rank : Function.Surjective (mfderiv (𝓘(ℝ, P)) (𝓘(ℝ, E)) (fun b => H (x, b)) a)) :
    Function.Surjective (mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, P)))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (fun z : M × P => (z.1, H z)) (x, a)) := by
  rw [mfderiv_prodMk mdifferentiableAt_fst smooth]
  intro y
  change TangentSpace (𝓘(ℝ, E)) x × TangentSpace (𝓘(ℝ, E)) (H (x, a)) at y
  obtain ⟨v, hv⟩ := rank (y.2 - mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun z => H (z, a)) x y.1)
  refine ⟨(y.1, v), ?_⟩
  apply Prod.ext
  · change mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, P))) (𝓘(ℝ, E)) Prod.fst (x, a) (y.1, v) = y.1
    rw [mfderiv_fst]
    rfl
  · change mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, P))) (𝓘(ℝ, E)) H (x, a) (y.1, v) = y.2
    erw [mfderiv_prod_eq_add_apply smooth, hv]
    rw [add_comm, sub_add_cancel]

/-- The joint endpoint map is locally open at every full-control-rank C1
point, even when the number of controls exceeds the state dimension. -/
theorem endpoint_map_nhds_eq
    {E P M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [TopologicalSpace M] [ChartedSpace E M]
    {H : M × P → M} {x : M} {a : P}
    (smooth : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, P))) (𝓘(ℝ, E)) 1 H (x, a))
    (rank : Function.Surjective (mfderiv (𝓘(ℝ, P)) (𝓘(ℝ, E)) (fun b => H (x, b)) a)) :
    Filter.map (fun z : M × P => (z.1, H z)) (𝓝 (x, a)) = 𝓝 (x, H (x, a)) := by
  apply map_nhds_eq_of_mfderiv_surjective_boundaryless
    (I := (𝓘(ℝ, E)).prod (𝓘(ℝ, P))) (J := (𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
  · exact contMDiffAt_fst.prodMk smooth
  · exact endpoint_mfderiv_surjective (smooth.mdifferentiableAt one_ne_zero) rank
end LeanShared.SubmersionOpen
