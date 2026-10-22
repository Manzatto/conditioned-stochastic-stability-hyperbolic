module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicDerivativeError
public import LeanShared.Analysis.NonlinearHyperbolicWordJacobian
public import Mathlib.Algebra.BigOperators.Fin

/-! The constructed finite shooting dynamics have actual principal
Jacobian at most γ^N times their reference expanding determinant product.
All graph and derivative estimates are derived from their contraction data. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform.Data
open FiniteJetComposition
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

set_option maxHeartbeats 1600000 in
theorem exists_jacobian_radius (γ : ℝ) (hγ : 1 < γ) :
    ∃ η : ℝ, 0 < η ∧ ∀ N : ℕ, 0 < N → ∀ d : Data U S N,
      (d.k : ℝ) ≤ 1 / 4 → (d.δ : ℝ) ≤ η → ∀ z : U × S,
      (∀ i : Fin N, DifferentiableAt ℝ (d.nonlinear i) (d.evolve z i.val)) →
      |((ContinuousLinearMap.fst ℝ U S).comp
        ((fderiv ℝ (fun w => d.evolve w N) z).comp (ContinuousLinearMap.inl ℝ U S))).toLinearMap.det| ≤
        γ ^ N * ∏ i : Fin N, |(d.expanding i).toLinearMap.det| := by
  obtain ⟨η, positive, estimate⟩ := NonlinearHyperbolicWordJacobian.exists_radius (U := U) (S := S) γ hγ
  refine ⟨η, positive, fun N hN d hk hδ z smooth => ?_⟩
  let index : ℕ → Fin N := fun i => if h : i < N then ⟨i, h⟩ else ⟨0, hN⟩
  let A := fun i => d.expanding (index i)
  let B := fun i => d.contracting (index i)
  let H := fun i => if h : i < N then d.map ⟨i, h⟩ else id
  have same (n : ℕ) : word H n = fun w => d.evolve w n := by
    funext w
    induction n with
    | zero => rfl
    | succ n ih =>
      change H n (word H n w) = d.evolve w (n + 1)
      rw [ih]
      by_cases hn : n < N
      · simp only [H, dite_eq_left hn, evolve]
      · simp only [H, dite_eq_right hn, evolve, id_eq]
  have derivative (i : ℕ) (hi : i < N) : DifferentiableAt ℝ (H i) (word H i z) := by
    rw [same]
    simpa only [H, dite_eq_left hi] using d.map_differentiableAt ⟨i, hi⟩ _ (smooth ⟨i, hi⟩)
  have close (i : ℕ) (hi : i < N) :
      ‖fderiv ℝ (H i) (word H i z) - (A i).toContinuousLinearMap.prodMap (B i)‖ ≤ η := by
    rw [same]
    simpa only [H, A, B, index, dite_eq_left hi] using
      (d.derivative_error ⟨i, hi⟩ _ (smooth ⟨i, hi⟩)).trans hδ
  have result := estimate A B H z N
    (fun i => (ContinuousLinearMap.opNorm_le_of_lipschitzWith (d.inverse_bound (index i))).trans hk)
    (fun i => (ContinuousLinearMap.opNorm_le_of_lipschitzWith (d.stable_bound (index i))).trans hk)
    derivative close
  rw [same] at result
  have factors : (∏ i ∈ Finset.range N, |(A i).toLinearMap.det|) =
      ∏ i : Fin N, |(d.expanding i).toLinearMap.det| := by
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i _
    simp only [A, index, dite_eq_left i.isLt, Fin.eta]
  rw [factors] at result
  exact result

end LeanShared.FiniteBoundaryHyperbolicTransform.Data
