module

public import LeanShared.Analysis.HyperbolicWordPrincipalJacobian
public import LeanShared.Analysis.ChronologicalDerivativeProduct

/-! The principal Jacobian estimate applies to literal nonlinear finite
words with derivative control only along the actual finite trajectory. -/
public noncomputable section
namespace LeanShared.NonlinearHyperbolicWordJacobian
open GraphBlockJacobianProduct FiniteJetComposition
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem product_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L K : ℕ → E →L[ℝ] E) (n : ℕ) (same : ∀ i < n, L i = K i) : product L n = product K n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [product, product, same n (Nat.lt_succ_self n),
      ih (fun i hi => same i (hi.trans (Nat.lt_succ_self n)))]

theorem exists_radius (γ : ℝ) (hγ : 1 < γ) :
    ∃ η : ℝ, 0 < η ∧ ∀ A : ℕ → U ≃L[ℝ] U, ∀ B : ℕ → S →L[ℝ] S,
      ∀ H : ℕ → U × S → U × S, ∀ z : U × S, ∀ n : ℕ,
      (∀ i, ‖(A i).symm.toContinuousLinearMap‖ ≤ 1 / 4) →
      (∀ i, ‖B i‖ ≤ 1 / 4) →
      (∀ i < n, DifferentiableAt ℝ (H i) (word H i z)) →
      (∀ i < n, ‖fderiv ℝ (H i) (word H i z) - (A i).toContinuousLinearMap.prodMap (B i)‖ ≤ η) →
      |((ContinuousLinearMap.fst ℝ U S).comp
        ((fderiv ℝ (word H n) z).comp (ContinuousLinearMap.inl ℝ U S))).toLinearMap.det| ≤
        γ ^ n * ∏ i ∈ Finset.range n, |(A i).toLinearMap.det| := by
  obtain ⟨η, positive, estimate⟩ := HyperbolicWordPrincipalJacobian.exists_radius (U := U) (S := S) γ hγ
  refine ⟨η, positive, fun A B H z n hA hB smooth close => ?_⟩
  let L := fun i => if i < n then fderiv ℝ (H i) (word H i z)
    else (A i).toContinuousLinearMap.prodMap (B i)
  have bounds (i : ℕ) : ‖L i - (A i).toContinuousLinearMap.prodMap (B i)‖ ≤ η := by
    by_cases hi : i < n
    · simpa only [L, ite_eq_left hi] using close i hi
    · simp only [L, ite_eq_right hi, sub_self, norm_zero]
      exact positive.le
  have result := estimate A B L hA hB bounds n
  have same := product_congr L (fun i => fderiv ℝ (H i) (word H i z)) n
    (fun i hi => ite_eq_left hi)
  rw [same, ← (ChronologicalDerivativeProduct.hasFDerivAt_word H z n smooth).fderiv] at result
  exact result

end LeanShared.NonlinearHyperbolicWordJacobian
