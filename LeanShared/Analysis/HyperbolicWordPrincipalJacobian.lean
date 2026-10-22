module

public import LeanShared.Analysis.HyperbolicForwardGraphStep
public import LeanShared.Analysis.GraphBlockRelativeJacobian
public import LeanShared.Analysis.GraphBlockJacobianProduct

/-! Every sufficiently small perturbation of a uniformly hyperbolic block
sequence has unstable principal Jacobian bounded by γ^n times the actual
reference unstable determinant product. The moving graph sequence is
constructed internally, not assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicWordPrincipalJacobian
open GraphBlockPerturbation GraphBlockJacobianProduct
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

set_option maxHeartbeats 1600000 in
theorem exists_radius (γ : ℝ) (hγ : 1 < γ) :
    ∃ η : ℝ, 0 < η ∧ ∀ A : ℕ → U ≃L[ℝ] U, ∀ B : ℕ → S →L[ℝ] S,
      ∀ L : ℕ → U × S →L[ℝ] U × S,
      (∀ n, ‖(A n).symm.toContinuousLinearMap‖ ≤ 1 / 4) →
      (∀ n, ‖B n‖ ≤ 1 / 4) →
      (∀ n, ‖L n - (A n).toContinuousLinearMap.prodMap (B n)‖ ≤ η) →
      ∀ n, |((ContinuousLinearMap.fst ℝ U S).comp
        ((product L n).comp (ContinuousLinearMap.inl ℝ U S))).toLinearMap.det| ≤
        γ ^ n * ∏ i ∈ Finset.range n, |(A i).toLinearMap.det| := by
  obtain ⟨ε, positive, jacobian⟩ := GraphBlockRelativeJacobian.exists_radius (U := U) (S := S) γ hγ
  refine ⟨min ε (1 / 16), lt_min positive (by norm_num), fun A B L hA hB close => ?_⟩
  have step (n : ℕ) (G : {G : U →L[ℝ] S // ‖G‖ ≤ 1}) :=
    HyperbolicForwardGraphStep.exists_step (A n) (B n) (L n) G.val (hA n) (hB n)
      G.property (min ε (1 / 16)) (min_le_right _ _) (close n)
  choose C H actual inverse bounded action using step
  let sequence : ℕ → {G : U →L[ℝ] S // ‖G‖ ≤ 1} :=
    Nat.rec ⟨0, by simp only [norm_zero]; norm_num⟩ (fun n G => ⟨H n G, bounded n G⟩)
  let G := fun n => (sequence n).val
  let D := fun n => (C n (sequence n)).toContinuousLinearMap
  have initial : G 0 = 0 := rfl
  have intertwines : ∀ n, (L n).comp (graph (G n)) = (graph (G (n + 1))).comp (D n) :=
    fun n => action n (sequence n)
  have boundD (n : ℕ) : |(D n).toLinearMap.det| ≤ γ * |(A n).toLinearMap.det| := by
    have estimate := jacobian (A n) (B n) (L n) (G n)
      ((hA n).trans (by norm_num)) (sequence n).property ((close n).trans (min_le_left _ _))
    have same : D n = upper (L n) (G n) := actual n (sequence n)
    rw [same]
    exact estimate
  intro n
  rw [principal_eq L G D initial intertwines n, determinant_product]
  calc
    _ ≤ ∏ i ∈ Finset.range n, (γ * |(A i).toLinearMap.det|) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => boundD i)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

end LeanShared.HyperbolicWordPrincipalJacobian
