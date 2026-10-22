module
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Tactic.Ring

/-! Cone contraction accumulates through chronological linear words with
no constant for the number of charts or blocks. -/
public noncomputable section
namespace LeanShared.ProductConeWordBounds
open List
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
@[expose] def word : List ((X×Y) →L[ℝ] (X×Y)) → (X×Y) →L[ℝ] (X×Y)
  | [] => ContinuousLinearMap.id ℝ (X×Y)
  | B::tail => (word tail).comp B

theorem stable (q : ℝ) (nonneg : 0≤q) (blocks : List ((X×Y) →L[ℝ] (X×Y)))
    (step : ∀ B∈blocks, ∀ z, ‖(B z).1‖≤‖(B z).2‖ →
      ‖z.1‖≤‖z.2‖ ∧ ‖B z‖≤q*‖z‖)
    (z : X×Y) (target : ‖(word blocks z).1‖≤‖(word blocks z).2‖) :
    ‖z.1‖≤‖z.2‖ ∧ ‖word blocks z‖≤q^blocks.length*‖z‖ := by
  induction blocks generalizing z with
  | nil => simpa only [word,ContinuousLinearMap.id_apply,List.length_nil,pow_zero,one_mul] using And.intro target (le_refl ‖z‖)
  | cons B tail ih =>
    have tailStep : ∀ C∈tail, ∀ z, ‖(C z).1‖≤‖(C z).2‖ →
        ‖z.1‖≤‖z.2‖ ∧ ‖C z‖≤q*‖z‖ := fun C hC => step C (mem_cons_of_mem B hC)
    have result := ih tailStep (B z) target
    have first := step B (mem_cons_self) z result.1
    refine ⟨first.1,?_⟩
    change ‖word tail (B z)‖≤q^(tail.length+1)*‖z‖
    calc
      _ ≤ q^tail.length*‖B z‖ := result.2
      _ ≤ q^tail.length*(q*‖z‖) := mul_le_mul_of_nonneg_left first.2 (pow_nonneg nonneg _)
      _ = q^(tail.length+1)*‖z‖ := by rw [pow_succ]; ring

theorem inverse_unstable (q : ℝ) (nonneg : 0≤q) (blocks : List ((X×Y) →L[ℝ] (X×Y)))
    (step : ∀ B∈blocks, ∀ z, ‖z.2‖≤‖z.1‖ →
      ‖(B z).2‖≤‖(B z).1‖ ∧ ‖z‖≤q*‖B z‖)
    (z : X×Y) (input : ‖z.2‖≤‖z.1‖) :
    ‖(word blocks z).2‖≤‖(word blocks z).1‖ ∧ ‖z‖≤q^blocks.length*‖word blocks z‖ := by
  induction blocks generalizing z with
  | nil => simpa only [word,ContinuousLinearMap.id_apply,List.length_nil,pow_zero,one_mul] using And.intro input (le_refl ‖z‖)
  | cons B tail ih =>
    have tailStep : ∀ C∈tail, ∀ z, ‖z.2‖≤‖z.1‖ →
        ‖(C z).2‖≤‖(C z).1‖ ∧ ‖z‖≤q*‖C z‖ := fun C hC => step C (mem_cons_of_mem B hC)
    have first := step B (mem_cons_self) z input
    have result := ih tailStep (B z) first.1
    refine ⟨result.1,?_⟩
    change ‖z‖≤q^(tail.length+1)*‖word tail (B z)‖
    calc
      _ ≤ q*‖B z‖ := first.2
      _ ≤ q*(q^tail.length*‖word tail (B z)‖) := mul_le_mul_of_nonneg_left result.2 nonneg
      _ = q^(tail.length+1)*‖word tail (B z)‖ := by rw [pow_succ]; ring
end LeanShared.ProductConeWordBounds
