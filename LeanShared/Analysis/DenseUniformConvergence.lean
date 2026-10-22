module
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Complex.Basic

/-! Uniformly bounded operators converging on a dense set converge everywhere. -/
public noncomputable section
open Filter
open scoped Topology
namespace LeanShared.DenseUniformConvergence

variable {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℂ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem tendsto (T : ℕ → X →L[ℂ] Y) (S : X →L[ℂ] Y) (C : ℝ) (bound : ∀ n, ‖T n‖ ≤ C)
    {D : Set X} (dense : Dense D) (conv : ∀ d ∈ D, Tendsto (fun n => T n d) atTop (𝓝 (S d)))
    (x : X) : Tendsto (fun n => T n x) atTop (𝓝 (S x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have C0 : 0 ≤ C := (norm_nonneg _).trans (bound 0)
  set δ := ε / (3 * (C + ‖S‖ + 1)) with hδ
  have δ0 : 0 < δ := by positivity
  obtain ⟨d, close, hd⟩ := Metric.dense_iff.mp dense x δ δ0
  have close' : ‖x - d‖ < δ := by
    rw [← dist_eq_norm, dist_comm]; exact Metric.mem_ball.mp close
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (conv d hd) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖T n x - T n d‖ ≤ C * δ := by
    rw [← map_sub]
    exact ((T n).le_opNorm _).trans (mul_le_mul (bound n) close'.le (norm_nonneg _) C0)
  have h2 : ‖S d - S x‖ ≤ ‖S‖ * δ := by
    rw [← map_sub, ← norm_neg, ← map_neg, neg_sub]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left close'.le (norm_nonneg _))
  have h3 : ‖T n d - S d‖ < ε / 3 := by rw [← dist_eq_norm]; exact hN n hn
  rw [dist_eq_norm]
  have split : T n x - S x = (T n x - T n d) + (T n d - S d) + (S d - S x) := by abel
  rw [split]
  have sum : C * δ + ‖S‖ * δ < ε / 3 + ε / 3 := by
    have : (C + ‖S‖) * δ ≤ ε / 3 := by
      rw [hδ]
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg S]
    nlinarith
  calc ‖T n x - T n d + (T n d - S d) + (S d - S x)‖
      ≤ ‖T n x - T n d‖ + ‖T n d - S d‖ + ‖S d - S x‖ := norm_add₃_le
    _ < C * δ + ε / 3 + ‖S‖ * δ := by linarith
    _ < ε := by linarith

end LeanShared.DenseUniformConvergence
