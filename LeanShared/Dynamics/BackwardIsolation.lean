module

public import LeanShared.Dynamics.RobustFiniteIsolation

/-!
# Random backward segments and finite isolation

Forward errors of a backward trajectory control its inverse errors through
uniform continuity of the inverse homeomorphism. Reindexing a long backward
trajectory gives both halves of the finite-isolation segment. No random
stable-manifold or positivity conclusion is assumed.
-/

@[expose] public section

open Set Metric

namespace LeanShared

variable {X : Type*} [MetricSpace X]

/-- Forward closeness controls inverse-step closeness, with one common
tolerance for all pairs of points. -/
theorem exists_uniform_inverse_step_tolerance (T : X ≃ₜ X)
    (hTi : UniformContinuous (T.symm : X → X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : X,
      dist (T x) y < δ → dist x (T.symm y) < ε := by
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuous_iff.mp hTi ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  simpa only [T.symm_apply_apply] using huc hxy

/-- The robust isolation lemma only needs forward noise error, even for its
backward half. The inverse-error condition is derived rather than added. -/
theorem exists_pos_finite_isolation_of_forward_errors (T : X ≃ₜ X) {K U : Set X}
    (hT : UniformContinuous (T : X → X)) (hTi : UniformContinuous (T.symm : X → X))
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℕ → X,
      a 0 = b 0 →
      (∀ n ≤ N, a n ∈ K) → (∀ n ≤ N, b n ∈ K) →
      (∀ n < N, dist (a (n + 1)) (T (a n)) < δ) →
      (∀ n < N, dist (T (b (n + 1))) (b n) < δ) → a 0 ∈ U := by
  obtain ⟨N, hN, ε, hε, hiso⟩ :=
    exists_pos_robust_finite_isolation T hT hTi hK hU hcore
  obtain ⟨η, hη, hinv⟩ := exists_uniform_inverse_step_tolerance T hTi hε
  refine ⟨N, hN, min ε η, lt_min hε hη, ?_⟩
  intro a b hab ha hb hsa hsb
  exact hiso a b hab ha hb
    (fun n hn => (hsa n hn).trans_le (min_le_left _ _))
    (fun n hn => hinv _ _ ((hsb n hn).trans_le (min_le_right _ _)))

/-- Every sufficiently far point of a backward pseudo-orbit that stays in
the isolating neighborhood lies near the isolated core. This is the random
finite-segment deduction needed before the paper's cited plaque theorem. -/
theorem exists_pos_backward_tail_isolation (T : X ≃ₜ X) {K U : Set X}
    (hT : UniformContinuous (T : X → X)) (hTi : UniformContinuous (T.symm : X → X))
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℕ → X,
      (∀ j, z j ∈ K) →
      (∀ j, dist (T (z (j + 1))) (z j) < δ) →
      ∀ j, N ≤ j → z j ∈ U := by
  obtain ⟨N, hN, δ, hδ, hiso⟩ :=
    exists_pos_finite_isolation_of_forward_errors T hT hTi hK hU hcore
  refine ⟨N, hN, δ, hδ, ?_⟩
  intro z hz hstep j hj
  let a : ℕ → X := fun n => z (j - n)
  let b : ℕ → X := fun n => z (j + n)
  have he : a 0 = b 0 := by simp [a, b]
  have hsa : ∀ n < N, dist (a (n + 1)) (T (a n)) < δ := by
    intro n hn
    have hexp : j - (n + 1) + 1 = j - n := by omega
    simpa only [a, hexp, dist_comm] using hstep (j - (n + 1))
  have hsb : ∀ n < N, dist (T (b (n + 1))) (b n) < δ := by
    intro n _
    simpa only [b, Nat.add_assoc] using hstep (j + n)
  simpa only [a, Nat.sub_zero] using
    hiso a b he (fun n _ => hz _) (fun n _ => hz _) hsa hsb

/-- Compact metric ambient spaces supply both uniform-continuity inputs. -/
theorem exists_pos_backward_tail_isolation_of_compact [CompactSpace X]
    (T : X ≃ₜ X) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℕ → X,
      (∀ j, z j ∈ K) →
      (∀ j, dist (T (z (j + 1))) (z j) < δ) →
      ∀ j, N ≤ j → z j ∈ U :=
  exists_pos_backward_tail_isolation T
    (CompactSpace.uniformContinuous_of_continuous T.continuous)
    (CompactSpace.uniformContinuous_of_continuous T.symm.continuous) hK hU hcore

/-- The manuscript's uniform `C * epsilon` map error gives one common
small-noise threshold and tail index for every contained backward orbit. -/
theorem exists_small_noise_backward_tail_isolation [CompactSpace X]
    (T : X ≃ₜ X) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U)
    (Ω : ℝ → Type*) (F : (ε : ℝ) → Ω ε → X → X)
    {C : ℝ} (hC : 0 ≤ C)
    (hnoise : ∀ ε > 0, ∀ ω : Ω ε, ∀ x ∈ K, dist (F ε ω x) (T x) ≤ C * ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε < ε₀ → ∀ ω : ℕ → Ω ε, ∀ z : ℕ → X,
        (∀ j, z j ∈ K) → (∀ j, F ε (ω j) (z (j + 1)) = z j) →
        ∀ j, N ≤ j → z j ∈ U := by
  obtain ⟨N, hN, δ, hδ, hiso⟩ :=
    exists_pos_backward_tail_isolation_of_compact T hK hU hcore
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨N, hN, δ / (C + 1), div_pos hδ hC1, ?_⟩
  intro ε hε hsmall ω z hz horbit
  apply hiso z hz
  intro j
  have hprod : ε * (C + 1) < δ := (lt_div_iff₀ hC1).mp hsmall
  calc
    dist (T (z (j + 1))) (z j) =
        dist (F ε (ω j) (z (j + 1))) (T (z (j + 1))) := by
          rw [horbit j, dist_comm]
    _ ≤ C * ε := hnoise ε hε (ω j) _ (hz (j + 1))
    _ < δ := by nlinarith

end LeanShared
