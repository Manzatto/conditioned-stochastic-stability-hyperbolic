module
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Exponential closeness of hyperbolic orbit segments (the cone argument). Let
`W (m+1) = (A_m u_m + N_m(W_m).1, B_m s_m + N_m(W_m).2)` with `‖A_m⁻¹‖, ‖B_m‖ ≤ k`,
`‖N_m(W_m)‖ ≤ δ ‖W_m‖`, `k + δ < 1`, in the sup norm on `U × S`. If `‖W_m‖ ≤ ρ` for
`m ≤ n`, then `‖W_m‖ ≤ ρ (θ^m + θ^(n-m))` with `θ = max (k + δ) (k / (1 - k δ)) < 1`:
strictly unstable points stay strictly unstable and expand, the others contract. -/
public noncomputable section
open scoped NNReal
namespace LeanShared.HyperbolicConeCloseness

variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The closeness rate. -/
@[expose] def rate (k δ : ℝ) : ℝ := max (k + δ) (k / (1 - k * δ))

theorem rate_nonneg (k δ : ℝ) (hk : 0 ≤ k) (hδ : 0 ≤ δ) : 0 ≤ rate k δ :=
  le_max_of_le_left (add_nonneg hk hδ)

theorem rate_lt_one (k δ : ℝ) (hk : 0 ≤ k) (hδ : 0 ≤ δ) (small : k + δ < 1) :
    rate k δ < 1 := by
  have hkδ : k * δ < 1 := by nlinarith
  apply max_lt small
  rw [div_lt_one (by linarith)]
  nlinarith

theorem closeness (A : ℕ → U ≃L[ℝ] U) (B : ℕ → S →L[ℝ] S) (k δ : ℝ) (hk : 0 ≤ k) (hδ : 0 ≤ δ)
    (small : k + δ < 1)
    (hA : ∀ m, ‖(A m).symm.toContinuousLinearMap‖ ≤ k) (hB : ∀ m, ‖B m‖ ≤ k)
    (N : ℕ → U × S → U × S) (W : ℕ → U × S) (n : ℕ)
    (step : ∀ m < n, W (m + 1) = ((A m) (W m).1 + (N m (W m)).1, (B m) (W m).2 + (N m (W m)).2))
    (nonlinear : ∀ m < n, ‖N m (W m)‖ ≤ δ * ‖W m‖) (ρ : ℝ) (bound : ∀ m ≤ n, ‖W m‖ ≤ ρ) :
    ∀ m ≤ n, ‖W m‖ ≤ ρ * (rate k δ ^ m + rate k δ ^ (n - m)) := by
  set θ := rate k δ
  set θu := k / (1 - k * δ)
  have hkδ : k * δ < 1 := by nlinarith
  have hθu : θu ≤ θ := le_max_right _ _
  have hθs : k + δ ≤ θ := le_max_left _ _
  have θu_nonneg : 0 ≤ θu := div_nonneg hk (by linarith)
  have θu_lt : θu < 1 := lt_of_le_of_lt hθu (rate_lt_one k δ hk hδ small)
  let u : ℕ → ℝ := fun m => ‖(W m).1‖
  let s : ℕ → ℝ := fun m => ‖(W m).2‖
  have norm_eq (m : ℕ) : ‖W m‖ = max (u m) (s m) := Prod.norm_def _
  -- the two one-step inequalities
  have stableStep (m : ℕ) (hm : m < n) : s (m + 1) ≤ k * s m + δ * ‖W m‖ := by
    simp only [s]
    rw [step m hm]
    calc ‖(B m) (W m).2 + (N m (W m)).2‖ ≤ ‖(B m) (W m).2‖ + ‖(N m (W m)).2‖ := norm_add_le _ _
      _ ≤ k * ‖(W m).2‖ + δ * ‖W m‖ := by
          refine add_le_add (((B m).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _))) ?_
          exact (norm_snd_le _).trans (nonlinear m hm)
  have unstableStep (m : ℕ) (hm : m < n) : u m ≤ k * (u (m + 1) + δ * ‖W m‖) := by
    have identity : (W m).1 = (A m).symm ((W (m + 1)).1 - (N m (W m)).1) := by
      rw [step m hm]
      simp only [add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply]
    simp only [u]
    rw [identity]
    calc ‖(A m).symm ((W (m + 1)).1 - (N m (W m)).1)‖
        ≤ ‖(A m).symm.toContinuousLinearMap‖ * ‖(W (m + 1)).1 - (N m (W m)).1‖ :=
          (A m).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ k * (‖(W (m + 1)).1‖ + δ * ‖W m‖) := by
          refine mul_le_mul (hA m) ?_ (norm_nonneg _) hk
          refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
          exact (norm_fst_le _).trans (nonlinear m hm)
  -- strictly unstable points expand and stay strictly unstable
  have expand (m : ℕ) (hm : m < n) (su : s m < u m) :
      s (m + 1) < u (m + 1) ∧ u m ≤ θu * u (m + 1) := by
    have hW : ‖W m‖ = u m := by rw [norm_eq, max_eq_left su.le]
    have upos : 0 < u m := lt_of_le_of_lt (norm_nonneg _) su
    have key := unstableStep m hm
    rw [hW] at key
    have growth : u m ≤ θu * u (m + 1) := by
      simp only [θu]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    have larger : u m ≤ u (m + 1) := by
      have := mul_le_mul_of_nonneg_right θu_lt.le (norm_nonneg (W (m + 1)).1)
      simp only [u] at growth this ⊢
      linarith
    refine ⟨?_, growth⟩
    have := stableStep m hm
    rw [hW] at this
    have : s (m + 1) ≤ (k + δ) * u m := by nlinarith [norm_nonneg (W m).2]
    nlinarith
  have propagate : ∀ t m, m + t ≤ n → s m < u m → s (m + t) < u (m + t) ∧
      u m ≤ θu ^ t * u (m + t) := by
    intro t
    induction t with
    | zero => intro m _ su; simp only [add_zero, pow_zero, one_mul]; exact ⟨su, le_rfl⟩
    | succ t ih =>
      intro m hmt su
      obtain ⟨su', growth⟩ := ih m (by omega) su
      obtain ⟨su'', growth'⟩ := expand (m + t) (by omega) su'
      refine ⟨by rw [← add_assoc]; exact su'', ?_⟩
      rw [← add_assoc, pow_succ, mul_assoc]
      exact growth.trans (mul_le_mul_of_nonneg_left growth' (pow_nonneg θu_nonneg t))
  -- weakly stable points contract from the start
  have contract : ∀ m ≤ n, ¬ s m < u m → s m ≤ (k + δ) ^ m * s 0 := by
    intro m
    induction m with
    | zero => intro _ _; simp only [pow_zero, one_mul, le_refl]
    | succ m ih =>
      intro hm notsu
      have previous : ¬ s m < u m := by
        intro su
        exact notsu ((propagate 1 m (by omega) su).1)
      have bound' := ih (by omega) previous
      have hW : ‖W m‖ = s m := by rw [norm_eq, max_eq_right (not_lt.mp previous)]
      have one := stableStep m (by omega)
      rw [hW] at one
      calc s (m + 1) ≤ (k + δ) * s m := by linarith
        _ ≤ (k + δ) * ((k + δ) ^ m * s 0) :=
            mul_le_mul_of_nonneg_left bound' (by linarith)
        _ = (k + δ) ^ (m + 1) * s 0 := by ring
  intro m hm
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans (bound 0 (Nat.zero_le _))
  by_cases su : s m < u m
  · obtain ⟨_, growth⟩ := propagate (n - m) m (by omega) su
    rw [show m + (n - m) = n by omega] at growth
    have hW : ‖W m‖ = u m := by rw [norm_eq, max_eq_left su.le]
    have un : u n ≤ ρ := (norm_fst_le _).trans (bound n le_rfl)
    rw [hW]
    calc u m ≤ θu ^ (n - m) * u n := growth
      _ ≤ θ ^ (n - m) * ρ :=
          mul_le_mul (pow_le_pow_left₀ θu_nonneg hθu _) un (norm_nonneg _)
            (pow_nonneg (rate_nonneg k δ hk hδ) _)
      _ ≤ ρ * (θ ^ m + θ ^ (n - m)) := by
          have : 0 ≤ θ ^ m := pow_nonneg (rate_nonneg k δ hk hδ) _
          nlinarith
  · have hW : ‖W m‖ = s m := by rw [norm_eq, max_eq_right (not_lt.mp su)]
    have s0 : s 0 ≤ ρ := (norm_snd_le _).trans (bound 0 (Nat.zero_le _))
    rw [hW]
    calc s m ≤ (k + δ) ^ m * s 0 := contract m hm su
      _ ≤ θ ^ m * ρ := mul_le_mul (pow_le_pow_left₀ (by linarith) hθs _) s0 (norm_nonneg _)
            (pow_nonneg (rate_nonneg k δ hk hδ) _)
      _ ≤ ρ * (θ ^ m + θ ^ (n - m)) := by
          have : 0 ≤ θ ^ (n - m) := pow_nonneg (rate_nonneg k δ hk hδ) _
          nlinarith

end LeanShared.HyperbolicConeCloseness
