module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniApplication

/-! # Generalized simplicity from the KL rank-one Riesz projector

Commutation, idempotence and identity on ordinary eigenvectors imply identity
on every generalized eigenvector. Rank one therefore gives algebraic, not
merely geometric, simplicity without adding a new spectral input.
-/

@[expose] public noncomputable section
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.ProjectorGeneralizedSimplicity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fixes_nilpotent_vectors
    (T J : E →L[ℂ] E)
    (hidem : ∀ x, J (J x) = J x)
    (hcomm : ∀ x, T (J x) = J (T x))
    (hker : ∀ x, T x = 0 → J x = x) :
    ∀ k : ℕ, ∀ x, (T ^ k) x = 0 → J x = x := by
  intro k
  induction k with
  | zero =>
      intro x hx
      have hz : x = 0 := by simpa using hx
      simp [hz]
  | succ k ih =>
      intro x hx
      have hw : (T ^ k) (T x) = 0 := by
        rw [← mul_apply_eq_comp, ← pow_succ]
        exact hx
      have hfix := ih (T x) hw
      have hres : T (x - J x) = 0 := by
        rw [map_sub, hcomm, hfix, sub_self]
      have hp := hker (x - J x) hres
      rw [map_sub, hidem, sub_self] at hp
      exact (sub_eq_zero.mp hp.symm).symm

end ConditionedStochasticStabilityHyperbolic.ProjectorGeneralizedSimplicity

namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

/-- The KL output already proves that every generalized leading vector lies
in the same one-dimensional eigenspace; Jordan chains are excluded. -/
theorem ProjectorOutputs.generalized_leading_simple
    (o : ProjectorOutputs P i d q δ) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (k : ℕ) (x : E)
    (hx : ((P ε - o.eigenvalue ε • 1) ^ k) x = 0) :
    ∃ c : ℂ, x = c • o.vector ε := by
  let T := P ε - o.eigenvalue ε • (1 : E →L[ℂ] E)
  have hidem : ∀ x, o.projection ε (o.projection ε x) = o.projection ε x := by
    intro x
    rw [o.rank_one ε hε]
    simp only [ContinuousLinearMap.smulRight_apply, map_smul, o.normalization ε hε,
      one_smul]
  have hcomm : ∀ x, T (o.projection ε x) = o.projection ε (T x) := by
    intro x
    have he := congrArg (fun A : E →L[ℂ] E => A x) (o.projection_commutes ε hε)
    simp only [mul_apply_eq_comp] at he
    simpa only [T, sub_apply, smul_apply,
      one_apply_eq_self, map_sub, map_smul] using
      congrArg (fun y => y - o.eigenvalue ε • o.projection ε x) he
  have hker : ∀ x, T x = 0 → o.projection ε x = x := by
    intro x hx
    apply o.project_eigenvector ε hε (o.eigenvalue ε) (o.eigenvalue_near ε hε).le x
    have he : P ε x - o.eigenvalue ε • x = 0 := by simpa [T] using hx
    exact sub_eq_zero.mp he
  have hfix := ProjectorGeneralizedSimplicity.fixes_nilpotent_vectors T
    (o.projection ε) hidem hcomm hker k x hx
  refine ⟨o.mean ε x, ?_⟩
  calc
    x = o.projection ε x := hfix.symm
    _ = o.mean ε x • o.vector ε := by
      rw [o.rank_one ε hε, ContinuousLinearMap.smulRight_apply]

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
