module

public import LeanShared.Geometry.CoherentCenteredMapDynamics
public import LeanShared.Dynamics.FiniteBoundaryHyperbolicShooting

/-! Actual finite manifold trajectories remaining in the coherent chart tube
are encoded by the constructed shooting dynamics. This proves containment
in a shooting cylinder, the direction needed for volume upper estimates. -/
public noncomputable section
namespace LeanShared.CoherentFiniteOrbitEncoding
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
open CoherentCenteredCoordinateMaps
variable {E M U S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup S] [NormedSpace ℝ S]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {H : M → M} {K : Set M} {B δ : ℝ} {p : ℕ}

theorem evolve_coordinate
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := U × S) (Q := U × S) H K B δ)
    (frame : ∀ x : K, (U × S) ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (preserves : MapsTo H K K) (reference : Fin (p + 1) → K)
    (step : ∀ i : Fin p, advance preserves (reference ⟨i.val, by omega⟩) = reference ⟨i.val + 1, by omega⟩)
    (q : FiniteBoundaryHyperbolicTransform.Data U S p)
    (agreement : ∀ i z, ‖z‖ ≤ d.radius →
      q.map i z = localMap d frame preserves (reference ⟨i.val, by omega⟩) z)
    (y : M)
    (sources : ∀ j (hj : j ≤ p), H^[j] y ∈ (chart d (reference ⟨j, by omega⟩)).source)
    (bounded : ∀ j (hj : j ≤ p), ‖coordinate d frame (reference ⟨j, by omega⟩) (H^[j] y)‖ ≤ d.radius)
    (j : ℕ) (hj : j ≤ p) :
    q.evolve (coordinate d frame (reference ⟨0, Nat.zero_lt_succ p⟩) y) j =
      coordinate d frame (reference ⟨j, by omega⟩) (H^[j] y) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have before : j < p := by omega
    have previous : j ≤ p := by omega
    rw [q.evolve_step _ ⟨j, before⟩, ih previous,
      agreement _ _ (bounded j previous), localMap_step _ _ _ _ _ (sources j previous),
      step ⟨j, before⟩, Function.iterate_succ_apply']

theorem subset_shooting_cylinder
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := U × S) (Q := U × S) H K B δ)
    (frame : ∀ x : K, (U × S) ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (preserves : MapsTo H K K) (reference : Fin (p + 1) → K)
    (step : ∀ i : Fin p, advance preserves (reference ⟨i.val, by omega⟩) = reference ⟨i.val + 1, by omega⟩)
    (q : FiniteBoundaryHyperbolicTransform.Data U S p)
    (agreement : ∀ i z, ‖z‖ ≤ d.radius →
      q.map i z = localMap d frame preserves (reference ⟨i.val, by omega⟩) z)
    (r : ℝ) (W : Set M)
    (sources : ∀ y ∈ W, ∀ j (hj : j ≤ p), H^[j] y ∈ (chart d (reference ⟨j, by omega⟩)).source)
    (bounded : ∀ y ∈ W, ∀ j (hj : j ≤ p),
      ‖coordinate d frame (reference ⟨j, by omega⟩) (H^[j] y)‖ ≤ d.radius)
    (endpoints : ∀ y ∈ W,
      ‖coordinate d frame (reference ⟨p, Nat.lt_succ_self p⟩) (H^[p] y)‖ < r ∧
      ‖coordinate d frame (reference ⟨0, Nat.zero_lt_succ p⟩) y‖ < r) :
    W ⊆ decode d frame (reference ⟨0, Nat.zero_lt_succ p⟩) '' (q.shooting ⁻¹' Metric.ball 0 r) := by
  intro y hy
  let z := coordinate d frame (reference ⟨0, Nat.zero_lt_succ p⟩) y
  refine ⟨z, ?_, decode_coordinate d frame _ y (sources y hy 0 (Nat.zero_le p))⟩
  have evolve := evolve_coordinate d frame preserves reference step q agreement y
    (sources y hy) (bounded y hy) p le_rfl
  change dist (q.shooting z) 0 < r
  rw [dist_zero_right]
  rw [FiniteBoundaryHyperbolicTransform.Data.shooting, Prod.norm_def, evolve]
  exact max_lt
    ((norm_fst_le (coordinate d frame (reference ⟨p, Nat.lt_succ_self p⟩) (H^[p] y))).trans_lt
      (endpoints y hy).1)
    ((norm_snd_le z).trans_lt (endpoints y hy).2)

end LeanShared.CoherentFiniteOrbitEncoding
