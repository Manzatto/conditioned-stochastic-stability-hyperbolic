module

public import LeanShared.Dynamics.HyperbolicFramedBlockJacobian
public import LeanShared.Geometry.CoherentCenteredMapDynamics
public import LeanShared.Dynamics.FiniteBoundaryHyperbolicShooting
public import Mathlib.Algebra.BigOperators.Fin

/-! The entire reference determinant product in finite shooting is the
literal one-step unstable Jacobian over the whole manifold orbit segment. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
open CoherentCenteredCoordinateMaps

private theorem blocks_product {R : Type*} [CommMonoid R] (f : ℕ → R) (N p : ℕ) :
    (∏ i ∈ Finset.range p, ∏ j ∈ Finset.range N, f (N * i + j)) =
      ∏ j ∈ Finset.range (N * p), f j := by
  induction p with
  | zero => simp only [Finset.range_zero, Finset.prod_empty, mul_zero]
  | succ p ih => rw [Finset.prod_range_succ, ih, Nat.mul_succ, Finset.prod_range_add]

set_option maxHeartbeats 1600000 in
theorem IsometricFraming.finite_reference_product
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
    (a : IsometricFraming h)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (N p : ℕ) (x : Λ) (preserves : MapsTo ((T^N : M ≃ₜ M) : M → M) Λ Λ)
    (q : FiniteBoundaryHyperbolicTransform.Data
      (EuclideanSpace ℝ (Fin a.unstableDimension)) (EuclideanSpace ℝ (Fin a.stableDimension)) p)
    (actual : ∀ i z, (a.whole (advance preserves (h.iteratePoint (N * i.val) x))).symm
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M)
        (h.iteratePoint (N * i.val) x).val (a.whole (h.iteratePoint (N * i.val) x) z)) =
      (q.expanding i z.1, q.contracting i z.2)) :
    (∏ i : Fin p, |(q.expanding i).toLinearMap.det|) =
      ∏ j ∈ Finset.range (N * p), h.unstableJacobian ((T : M → M)^[j] x.val) := by
  have factor (i : Fin p) : |(q.expanding i).toLinearMap.det| =
      ∏ j ∈ Finset.range N, h.unstableJacobian ((T : M → M)^[N * i.val + j] x.val) := by
    let reference := h.iteratePoint (N * i.val) x
    have target : advance preserves reference = h.iteratePoint N reference := Subtype.ext rfl
    have action := actual i
    change ∀ z, (a.whole (advance preserves reference)).symm
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M)
        reference.val (a.whole reference z)) = (q.expanding i z.1, q.contracting i z.2) at action
    rw [target] at action
    apply (a.expanding_abs_det forward inverse N reference (q.expanding i).toContinuousLinearMap
      (q.contracting i) action).trans
    apply Finset.prod_congr rfl
    intro j _
    apply congrArg h.unstableJacobian
    change (T : M → M)^[j] ((T^(N * i.val)) x.val) = _
    rw [DiffeomorphismIterates.coe_pow, ← Function.iterate_add_apply, Nat.add_comm]
  rw [← blocks_product (fun j => h.unstableJacobian ((T : M → M)^[j] x.val)) N p,
    ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  exact factor i

end LeanShared.HyperbolicBasicSet
