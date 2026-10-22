module

public import LeanShared.Geometry.CoherentCenteredDecodeDynamics
public import LeanShared.Dynamics.FiniteBoundaryHyperbolicShooting

/-! Constructed finite coordinate segments decode to literal iterates of
the original manifold map, in the coherently chosen incoming/outgoing charts. -/
public noncomputable section
namespace LeanShared.CoherentFiniteOrbitDecoding
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
open CoherentCenteredCoordinateMaps
variable {E M U S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup S] [NormedSpace ℝ S]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {H : M → M} {K : Set M} {B δ : ℝ} {p : ℕ}

theorem decode_evolve
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := U × S) (Q := U × S) H K B δ)
    (frame : ∀ x : K, (U × S) ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (preserves : MapsTo H K K)
    (forward : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B)
    (inverse : ∀ x, ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (reference : Fin (p + 1) → K)
    (step : ∀ i : Fin p, advance preserves (reference ⟨i.val, by omega⟩) = reference ⟨i.val + 1, by omega⟩)
    (q : FiniteBoundaryHyperbolicTransform.Data U S p)
    (agreement : ∀ i z, ‖z‖ ≤ d.radius →
      q.map i z = localMap d frame preserves (reference ⟨i.val, by omega⟩) z)
    (z : U × S) (bounded : ∀ j ≤ p, ‖q.evolve z j‖ ≤ d.radius)
    (j : ℕ) (hj : j ≤ p) :
    decode d frame (reference ⟨j, by omega⟩) (q.evolve z j) =
      H^[j] (decode d frame (reference ⟨0, Nat.zero_lt_succ p⟩) z) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have before : j < p := by omega
    have previous : j ≤ p := by omega
    rw [q.evolve_step z ⟨j, before⟩, agreement _ _ (bounded j previous),
      ← step ⟨j, before⟩, decode_localMap d frame preserves forward inverse _ _ (bounded j previous),
      ih previous, Function.iterate_succ_apply']

end LeanShared.CoherentFiniteOrbitDecoding
