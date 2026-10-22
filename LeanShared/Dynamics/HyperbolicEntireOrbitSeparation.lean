module
public import LeanShared.Dynamics.HyperbolicCoherentNonlinearCharts
public import LeanShared.Dynamics.HyperbolicChartOrbitUniqueness
public import Mathlib.Tactic.NormNum

/-! Actual compact hyperbolic basic-set data separate entire nearby orbits.
All coherent charts, the common nonlinear radius, and the bilateral
contraction are constructed internally from the actual C¹ diffeomorphism. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal
open LeanShared.CoherentCenteredCoordinateMaps

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_entire_orbit_separation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) :
    ∃ N : ℕ, 0 < N ∧ ∃ η : ℝ, 0 < η ∧
      ∀ reference : ℤ → Λ, (∀ n, (T^N) (reference (n + 1)).val = (reference n).val) →
      ∀ orbit : ℤ → M, (∀ n, (T^N) (orbit (n + 1)) = orbit n) →
      (∀ n, dist (reference n).val (orbit n) < η) → ∀ n, orbit n = (reference n).val := by
  obtain ⟨a, N, positiveN, B, positiveB, frameBounds, ⟨d⟩, blocks⟩ :=
    b.exists_coherent_nonlinear_charts forward inverse (1 / 4) (1 / 16) (by norm_num) (by norm_num)
  let k : ℝ≥0 := ⟨1 / 4, by norm_num⟩
  let δ : ℝ≥0 := ⟨1 / 16, by norm_num⟩
  let H := ((T^N : M ≃ₜ M) : M → M)
  have preserves : MapsTo H Λ Λ := by
    have step : MapsTo T Λ Λ := fun x hx => by
      rw [← b.hyperbolic.invariant]
      exact mem_image_of_mem T hx
    intro x hx
    change ((T^N : M ≃ₜ M) : M → M) x ∈ Λ
    rw [DiffeomorphismIterates.coe_pow]
    exact step.iterate N hx
  choose S U boundS boundU actual using blocks
  have linearization (x : Λ) :
      (a.whole (advance preserves x)).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (a.whole x).toContinuousLinearMap) =
      (U x).toContinuousLinearMap.prodMap (S x).toContinuousLinearMap := by
    have same : advance preserves x = b.hyperbolic.iteratePoint N x := Subtype.ext rfl
    apply ContinuousLinearMap.ext
    intro z
    change (a.whole (advance preserves x)).symm
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val (a.whole x z)) = (U x z.1, S x z.2)
    rw [same]
    exact actual x z
  obtain ⟨η, positiveη, separates⟩ := HyperbolicChartOrbitUniqueness.exists_separation_radius
    k δ d a.whole preserves positiveB (fun x => (frameBounds x).1) (fun x => (frameBounds x).2)
    U (fun x => (S x).toContinuousLinearMap) (by change (1 / 4 : ℝ) + (1 / 16) * 2 < 1; norm_num) boundU boundS linearization
  refine ⟨N, positiveN, η, positiveη, fun reference referenceStep orbit orbitStep close => ?_⟩
  exact separates reference (fun n => Subtype.ext (referenceStep n)) orbit orbitStep close

end LeanShared.HyperbolicBasicSet
