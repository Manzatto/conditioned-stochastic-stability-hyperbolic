module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! Exact transport of all derivative orders under a linear change of model.
The identities use linear equivalences and hold without extra smoothness
hypotheses, including at points where the derivative is defined by zero. -/

public noncomputable section
namespace LeanShared.LinearConjugateJets
open Function
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The linear action on the actual k-th derivative tensor. -/
def transport (e : E ≃L[ℝ] F) (k : ℕ) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E) →ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => F) F where
  toFun A := e.toContinuousLinearMap.compContinuousMultilinearMap
    (A.compContinuousLinearMap (fun _ => e.symm.toContinuousLinearMap))
  map_add' A B := by ext v; simp
  map_smul' c A := by ext v; simp

 theorem norm_transport_le (e : E ≃L[ℝ] F) (k : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) E) :
    ‖transport e k A‖ ≤ ‖e.toContinuousLinearMap‖ *
      ‖e.symm.toContinuousLinearMap‖ ^ k * ‖A‖ := by
  apply (e.toContinuousLinearMap.norm_compContinuousMultilinearMap_le _).trans
  have bound := A.norm_compContinuousLinearMap_le
    (fun _ : Fin k => e.symm.toContinuousLinearMap)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_left_comm,
    mul_comm, mul_assoc] using mul_le_mul_of_nonneg_left bound
      (norm_nonneg e.toContinuousLinearMap)

 theorem iteratedFDeriv_conjugate (e : E ≃L[ℝ] F) (f : E → E) (k : ℕ) (x : F) :
    iteratedFDeriv ℝ k (e ∘ f ∘ e.symm) x =
      transport e k (iteratedFDeriv ℝ k f (e.symm x)) := by
  rw [e.iteratedFDeriv_comp_left]
  have right := e.symm.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (Set.mem_univ (e.symm x)) k
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at right
  rw [right]
  rfl

 theorem norm_iterated_difference_le (e : E ≃L[ℝ] F) (f g : E → E) (k : ℕ)
    (x : F) :
    ‖iteratedFDeriv ℝ k (e ∘ f ∘ e.symm) x -
      iteratedFDeriv ℝ k (e ∘ g ∘ e.symm) x‖ ≤
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ^ k *
      ‖iteratedFDeriv ℝ k f (e.symm x) - iteratedFDeriv ℝ k g (e.symm x)‖ := by
  rw [iteratedFDeriv_conjugate, iteratedFDeriv_conjugate, ← map_sub]
  exact norm_transport_le e k _

 theorem norm_iterated_increment_difference_le (e : E ≃L[ℝ] F) (f g : E → E)
    (k : ℕ) (x y : F) :
    ‖(iteratedFDeriv ℝ k (e ∘ f ∘ e.symm) x -
        iteratedFDeriv ℝ k (e ∘ g ∘ e.symm) x) -
      (iteratedFDeriv ℝ k (e ∘ f ∘ e.symm) y -
        iteratedFDeriv ℝ k (e ∘ g ∘ e.symm) y)‖ ≤
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ^ k *
      ‖(iteratedFDeriv ℝ k f (e.symm x) - iteratedFDeriv ℝ k g (e.symm x)) -
        (iteratedFDeriv ℝ k f (e.symm y) - iteratedFDeriv ℝ k g (e.symm y))‖ := by
  simp only [iteratedFDeriv_conjugate, ← map_sub]
  exact norm_transport_le e k _

end LeanShared.LinearConjugateJets
