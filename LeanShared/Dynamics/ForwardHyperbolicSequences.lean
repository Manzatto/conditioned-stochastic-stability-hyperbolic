module
public import LeanShared.Dynamics.HyperbolicShadowing

/-! Forward-indexed hyperbolic sequences. For split maps
`W ↦ (A_i u + N_i(W).1, B_i s + N_i(W).2)` with `‖A_i⁻¹‖, ‖B_i‖ ≤ k` and
`δ`-Lipschitz `N_i`, `k + δ < 1`, there is a unique bounded forward orbit
`W (i+1) = map_i (W i)`, bounded by `(k+1) e / (1 - k - δ)` where `e` bounds `‖N_i 0‖`.
If the data are `n`-periodic, so is the orbit. This is the bilateral Lyapunov–Perron
contraction of `HyperbolicShadowing`, read backwards in time. -/
public noncomputable section
set_option linter.unusedSectionVars false
namespace LeanShared.ForwardHyperbolicSequences
open scoped NNReal BoundedContinuousFunction

variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/-- The forward split map. -/
@[expose] def step (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S) (N : ℤ → U × S → U × S)
    (i : ℤ) (w : U × S) : U × S :=
  ((A i) w.1 + (N i w).1, (B i) w.2 + (N i w).2)

/-- The backward-indexed shadowing data. -/
@[expose] def data (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S) (N : ℤ → U × S → U × S)
    (k δ : ℝ≥0) (small : k + δ < 1) (hA : ∀ i, LipschitzWith k (A i).symm)
    (hB : ∀ i, LipschitzWith k (B i)) (hN : ∀ i, LipschitzWith δ (N i)) (e : ℝ)
    (he : ∀ i, ‖N i 0‖ ≤ e) : HyperbolicShadowing.Data U S where
  expanding := fun n => A (-n - 1)
  contracting := fun n => B (-n - 1)
  nonlinear := fun n => N (-n - 1)
  k := k
  δ := δ
  small := small
  inverse_bound := fun n => hA (-n - 1)
  stable_bound := fun n => hB (-n - 1)
  nonlinear_bound := fun n => hN (-n - 1)
  error := e
  nonlinear_zero := fun n => he (-n - 1)

/-- Unique bounded forward orbits of hyperbolic split maps. -/
theorem exists_unique (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S) (N : ℤ → U × S → U × S)
    (k δ : ℝ≥0) (small : k + δ < 1) (hA : ∀ i, LipschitzWith k (A i).symm)
    (hB : ∀ i, LipschitzWith k (B i)) (hN : ∀ i, LipschitzWith δ (N i)) (e : ℝ)
    (he : ∀ i, ‖N i 0‖ ≤ e) :
    ∃ W : ℤ → U × S, (∀ i, W (i + 1) = step A B N i (W i)) ∧
      (∀ i, ‖W i‖ ≤ (((k : ℝ) + 1) * e) / (1 - (k + δ : ℝ≥0))) ∧
      ∀ W' : ℤ → U × S, (∃ R : ℝ, ∀ i, ‖W' i‖ ≤ R) →
        (∀ i, W' (i + 1) = step A B N i (W' i)) → W' = W := by
  let d := data A B N k δ small hA hB hN e he
  let z := d.orbit
  have bound := d.shadowing_bound
  refine ⟨fun i => z (-i), fun i => ?_, fun i => ?_, fun W' bounded equation => ?_⟩
  · have h := d.orbit_step (-i - 1)
    have index : -i - 1 + 1 = -i := by ring
    rw [index] at h
    have index' : -(i + 1) = -i - 1 := by ring
    change z (-(i + 1)) = step A B N i (z (-i))
    rw [index', ← h]
    change d.map (-i - 1) (z (-i)) = step A B N i (z (-i))
    simp only [step, HyperbolicShadowing.Data.map, d, data, neg_sub, sub_neg_eq_add]
    simp only [add_sub_cancel_left]
  · exact ((z.norm_coe_le_norm (-i)).trans bound)
  · obtain ⟨R, hR⟩ := bounded
    let z' : ℤ →ᵇ U × S := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun n => W' (-n)) R (fun n => hR (-n))
    have same : z' = z := by
      apply d.orbit_unique
      intro n
      change d.map n (W' (-(n + 1))) = W' (-n)
      have h := equation (-(n + 1))
      have index : -(n + 1) + 1 = -n := by ring
      rw [index] at h
      rw [h]
      simp only [step, HyperbolicShadowing.Data.map, d, data]
      have : -n - 1 = -(n + 1) := by ring
      rw [this]
    funext i
    have := congrArg (fun f : ℤ →ᵇ U × S => f (-i)) same
    simpa only [z', BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete, neg_neg] using this

/-- Periodic data have periodic bounded orbits. -/
theorem periodic (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S) (N : ℤ → U × S → U × S)
    (n : ℤ) (hAp : ∀ i, A (i + n) = A i) (hBp : ∀ i, B (i + n) = B i)
    (hNp : ∀ i, N (i + n) = N i) (W : ℤ → U × S)
    (equation : ∀ i, W (i + 1) = step A B N i (W i))
    (unique : ∀ W' : ℤ → U × S, (∃ R : ℝ, ∀ i, ‖W' i‖ ≤ R) →
      (∀ i, W' (i + 1) = step A B N i (W' i)) → W' = W)
    (bounded : ∃ R : ℝ, ∀ i, ‖W i‖ ≤ R) (i : ℤ) : W (i + n) = W i := by
  have shifted := unique (fun j => W (j + n)) (by
    obtain ⟨R, hR⟩ := bounded
    exact ⟨R, fun j => hR (j + n)⟩) (fun j => by
      have h := equation (j + n)
      rw [show j + n + 1 = j + 1 + n by ring] at h
      rw [h]
      simp only [step, hAp, hBp, hNp])
  exact congrFun shifted i

end LeanShared.ForwardHyperbolicSequences
