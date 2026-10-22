module
public import LeanShared.Dynamics.HyperbolicCoherentNonlinearCharts
public import LeanShared.Dynamics.HyperbolicFractionalBowenDistortion
public import Mathlib.Tactic.NormNum

/-! A literal compact hyperbolic basic set and an actually fractional
regular potential have uniform block Bowen distortion. All coordinates,
Hölder constants, derivative bounds, iterates and radii are derived internally. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal BigOperators
open LeanShared.CoherentCenteredCoordinateMaps

set_option maxHeartbeats 2400000 in
theorem BasicData.block_bowen_distortion
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ) :
    ∃ N : ℕ, 0 < N ∧ ∃ η > 0, ∃ D ≥ 0, ∀ reference : ℤ → Λ,
      (∀ j, (T ^ N) (reference (j + 1)).val = (reference j).val) →
      ∀ (orbit : ℤ → M) (n : ℕ),
      (∀ j : ℕ, j < n → (T ^ N) (orbit (j + 1)) = orbit j) →
      (∀ j : ℕ, j ≤ n → dist (reference j).val (orbit j) < η) →
      |(∑ j ∈ Finset.range (n + 1), ψ (orbit j)) -
        (∑ j ∈ Finset.range (n + 1), ψ (reference j).val)| ≤ D := by
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
  obtain ⟨η, positiveη, D, nonnegativeD, distortion⟩ :=
    HyperbolicChartOrbitUniqueness.fractional_energy_distortion
      k δ d a.whole preserves positiveB (fun x => (frameBounds x).1) (fun x => (frameBounds x).2)
      U (fun x => (S x).toContinuousLinearMap)
      (by change (1 / 4 : ℝ) + (1 / 16) * 2 < 1; norm_num)
      boundU boundS linearization ψ α positiveα smallα regular
  refine ⟨N, positiveN, η, positiveη, D, nonnegativeD, ?_⟩
  intro reference referenceStep orbit n orbitStep close
  exact distortion reference (fun j => Subtype.ext (referenceStep j)) orbit n orbitStep close

end LeanShared.HyperbolicBasicSet
