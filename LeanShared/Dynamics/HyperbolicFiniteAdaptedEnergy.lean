module

public import LeanShared.Analysis.FiniteAdaptedEnergy
public import LeanShared.Dynamics.HyperbolicBasicSet
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Tactic.Positivity

/-! Finite adapted quadratic energies for the actual manifold derivative cocycle. The terminal time
is selected from the literal exponential bound, rather than assumed. -/

public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators

namespace LeanShared.HyperbolicFiniteAdaptedEnergy

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

@[expose] def iterateEnergy (f : M → M) (a : ℝ) (N : ℕ)
    (x : M) (v : TangentSpace (𝓘(ℝ, E)) x) : ℝ :=
  FiniteAdaptedEnergy.energy ((a ^ 2)⁻¹)
    (fun j => ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j]) x v‖ ^ 2) N

theorem shift (f : M → M) (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 f)
    (a : ℝ) (N : ℕ) (x : M) (v : TangentSpace (𝓘(ℝ, E)) x) :
    iterateEnergy f a N (f x) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f x v) =
      FiniteAdaptedEnergy.energy ((a ^ 2)⁻¹)
        (fun j => ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j + 1]) x v‖ ^ 2) N := by
  unfold iterateEnergy FiniteAdaptedEnergy.energy
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [Function.iterate_succ,
    mfderiv_comp x ((smooth.iterate j).mdifferentiable one_ne_zero (f x))
      (smooth.mdifferentiable one_ne_zero x)]
  rfl

theorem zero_term (f : M → M) (x : M) (v : TangentSpace (𝓘(ℝ, E)) x) :
    ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[0]) x v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [Function.iterate_zero, mfderiv_id]
  rfl

theorem initial_le (f : M → M) (a : ℝ) (N : ℕ) (length : 0 < N)
    (x : M) (v : TangentSpace (𝓘(ℝ, E)) x) : ‖v‖ ^ 2 ≤ iterateEnergy f a N x v := by
  have result := FiniteAdaptedEnergy.initial_le ((a ^ 2)⁻¹) (inv_nonneg.mpr (sq_nonneg a))
    (fun j => ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j]) x v‖ ^ 2)
    (fun j => sq_nonneg _) N length
  simpa only [zero_term, iterateEnergy] using result

/-- One fixed time works uniformly over every vector in the prescribed
distribution, with a uniform upper comparison and one-step contraction. -/
theorem uniform_energy (f : M → M)
    (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 f)
    (K : Set M) (S : ∀ x, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x))
    (C q a : ℝ)
    (positiveA : 0 < a) (N : ℕ) (length : 0 < N)
    (terminal : C * q ^ N ≤ a ^ N)
    (bound : ∀ n : ℕ, ∀ x ∈ K, ∀ v ∈ S x,
      ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[n]) x v‖ ≤ C * q ^ n * ‖v‖) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ K, ∀ v ∈ S x,
      ‖v‖ ^ 2 ≤ iterateEnergy f a N x v ∧
      iterateEnergy f a N x v ≤ B * ‖v‖ ^ 2 ∧
      iterateEnergy f a N (f x) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f x v) ≤
        a ^ 2 * iterateEnergy f a N x v := by
  let weight := (a ^ 2)⁻¹
  let B := ∑ j ∈ Finset.range N, weight ^ j * (C * q ^ j) ^ 2
  have positiveWeight : 0 < weight := inv_pos.mpr (sq_pos_of_pos positiveA)
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro x hx v hv
  refine ⟨initial_le f a N length x v, ?_, ?_⟩
  · calc
      iterateEnergy f a N x v ≤
          ∑ j ∈ Finset.range N, weight ^ j * (C * q ^ j * ‖v‖) ^ 2 := by
        change (∑ j ∈ Finset.range N,
          weight ^ j * ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j]) x v‖ ^ 2) ≤ _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (bound j x hx v hv) 2)
          (pow_nonneg positiveWeight.le j)
      _ = B * ‖v‖ ^ 2 := by
        simp only [B, mul_pow, Finset.sum_mul, mul_assoc]
      _ ≤ max 1 B * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  · have atN : ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[N]) x v‖ ≤ a ^ N * ‖v‖ :=
      (bound N x hx v hv).trans (mul_le_mul_of_nonneg_right terminal (norm_nonneg v))
    have cancel : weight ^ N * (a ^ N) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm N 2, pow_mul, ← mul_pow]
      simp only [weight, inv_mul_cancel₀ (pow_ne_zero 2 positiveA.ne'), one_pow]
    have tail : weight ^ N * ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[N]) x v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      calc
        _ ≤ weight ^ N * (a ^ N * ‖v‖) ^ 2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) atN 2) (pow_nonneg positiveWeight.le N)
        _ = ‖v‖ ^ 2 := by rw [mul_pow, ← mul_assoc, cancel, one_mul]
    have contraction := FiniteAdaptedEnergy.contraction weight positiveWeight
      (fun j => ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j]) x v‖ ^ 2) N
      (by simpa only [zero_term] using tail)
    rw [shift f smooth]
    simpa only [iterateEnergy, weight, inv_inv] using contraction

/-- Uniform hyperbolicity selects one terminal time for both actual stable and
inverse-unstable cocycles. No adapted norm or terminal estimate is an input. -/
theorem HyperbolicData.exists_two_sided_energy [FiniteDimensional ℝ E]
    [IsManifold (𝓘(ℝ, E)) ∞ M]
    {T : M ≃ₜ M} {Λ : Set M}
    (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (slack : h.contraction < a) :
    ∃ N : ℕ, 0 < N ∧ ∃ Bs Bu : ℝ, 1 ≤ Bs ∧ 1 ≤ Bu ∧
      (∀ x ∈ Λ, ∀ v ∈ h.stable x,
        ‖v‖ ^ 2 ≤ iterateEnergy T a N x v ∧
        iterateEnergy T a N x v ≤ Bs * ‖v‖ ^ 2 ∧
        iterateEnergy T a N (T x) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v) ≤
          a ^ 2 * iterateEnergy T a N x v) ∧
      (∀ x ∈ Λ, ∀ v ∈ h.unstable x,
        ‖v‖ ^ 2 ≤ iterateEnergy T.symm a N x v ∧
        iterateEnergy T.symm a N x v ≤ Bu * ‖v‖ ^ 2 ∧
        iterateEnergy T.symm a N (T.symm x)
            (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm x v) ≤
          a ^ 2 * iterateEnergy T.symm a N x v) := by
  have positiveA : 0 < a := h.contraction_pos.trans slack
  obtain ⟨N, length, terminal⟩ := FiniteAdaptedEnergy.exists_terminal_time
    h.constant h.contraction a h.constant_pos h.contraction_pos.le positiveA slack
  obtain ⟨Bs, hBs, stable⟩ := uniform_energy T forward Λ h.stable
    h.constant h.contraction a positiveA N length terminal h.stable_bound
  obtain ⟨Bu, hBu, unstable⟩ := uniform_energy T.symm backward Λ h.unstable
    h.constant h.contraction a positiveA N length terminal h.unstable_bound
  exact ⟨N, length, Bs, Bu, hBs, hBu, stable, unstable⟩

end LeanShared.HyperbolicFiniteAdaptedEnergy
