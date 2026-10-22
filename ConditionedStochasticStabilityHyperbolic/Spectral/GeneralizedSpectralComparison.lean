module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ProjectorGeneralizedSimplicity
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedSpectralComparison

/-! # Algebraic simplicity through generalized retained spectral comparison

Common-region comparison lifts generalized physical vectors into the analytic
space. Geometric restriction need separate only those generalized eigenspaces.
Together with the KL rank-one Riesz projector, these conditions exclude Jordan
chains in the actual physical operator.
-/

@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.GeneralizedSpectralComparison

variable {A F W : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Precise common-region part of the classical generalized spectral
comparison theorem, at the eigenvalue under consideration. -/
def Comparison (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (a : A →L[ℂ] W) (b : F →L[ℂ] W) (z : ℂ) : Prop :=
  ∀ k : ℕ, ∀ f, f ≠ 0 → ((Q - z • 1) ^ k) f = 0 →
    ∃ v, ((P - z • 1) ^ k) v = 0 ∧ b f = a v

/-- Supplied by actual complement extinction and no-return restriction,
with no global injectivity requirement. -/
def Separates (Q : F →L[ℂ] F) (b : F →L[ℂ] W) (z : ℂ) : Prop :=
  ∀ k : ℕ, ∀ f, ((Q - z • 1) ^ k) f = 0 → b f = 0 → f = 0

theorem generalized_simple
    (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (a : A →L[ℂ] W) (b : F →L[ℂ] W) (z : ℂ)
    (hcompare : Comparison P Q a b z) (hsep : Separates Q b z)
    (γ : A) (g : F) (hg : Q g = z • g) (hident : b g = a γ)
    (hsimple : ∀ k : ℕ, ∀ v, ((P - z • 1) ^ k) v = 0 →
      ∃ c : ℂ, v = c • γ) :
    ∀ k : ℕ, ∀ f, ((Q - z • 1) ^ k) f = 0 → ∃ c : ℂ, f = c • g := by
  intro k f hf
  by_cases hzero : f = 0
  · exact ⟨0, by simp [hzero]⟩
  have hk : k ≠ 0 := by
    intro hzeroK
    exact hzero (by simpa [hzeroK] using hf)
  obtain ⟨v, hv, hfv⟩ := hcompare k f hzero hf
  obtain ⟨c, hc⟩ := hsimple k v hv
  have hchain : ((Q - z • 1) ^ k) g = 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have hone : (Q - z • 1) g = 0 := by
      simp only [sub_apply, smul_apply, one_apply_eq_self, hg, sub_self]
    rw [pow_succ, mul_apply_eq_comp, hone, map_zero]
  refine ⟨c, sub_eq_zero.mp (hsep k (f - c • g) ?_ ?_)⟩
  · rw [map_sub, map_smul, hf, hchain, smul_zero, sub_self]
  · rw [map_sub, map_smul, hfv, hc, map_smul, hident, sub_self]

/-- Scaling does not create Jordan chains at the scaled eigenvalue. -/
theorem generalized_simple_smul
    (P : A →L[ℂ] A) (z s : ℂ) (hs : s ≠ 0) (γ : A)
    (hsimple : ∀ k : ℕ, ∀ v, ((P - z • 1) ^ k) v = 0 →
      ∃ c : ℂ, v = c • γ) :
    ∀ k : ℕ, ∀ v, ((s • P - (s * z) • 1) ^ k) v = 0 →
      ∃ c : ℂ, v = c • γ := by
  intro k v hv
  apply hsimple k v
  have he : s • P - (s * z) • (1 : A →L[ℂ] A) = s • (P - z • 1) := by
    rw [smul_sub, smul_smul]
  rw [he, smul_pow, smul_apply] at hv
  exact (smul_eq_zero.mp hv).resolve_left (pow_ne_zero _ hs)

end ConditionedStochasticStabilityHyperbolic.GeneralizedSpectralComparison
