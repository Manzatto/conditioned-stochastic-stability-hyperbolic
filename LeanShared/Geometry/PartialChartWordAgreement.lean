module
public import LeanShared.Analysis.CylinderPrincipalCoefficient

/-! Exact cancellation of the genuine partial charts along a literal
physical cylinder. Only actual chart validity and one-step agreement on
the visited coordinate sets enter the proof. -/
public noncomputable section
namespace LeanShared.PartialChartWordAgreement
open Set CylinderPrincipalCoefficient
variable {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]

theorem prefix_eq {N : ℕ} (F : Fin N → M → M) (G : Fin N → E → E)
    (κ : ℕ → OpenPartialHomeomorph M E) (B : ℕ → Set E)
    (agreement : ∀ k : Fin N, ∀ z ∈ B k.val,
      G k z = κ (k.val+1) (F k ((κ k.val).symm z)))
    (m : M)
    (valid : ∀ k ≤ N, prefixOrbit F (fun j => j) k m ∈ (κ k).source)
    (tracking : ∀ k < N, κ k (prefixOrbit F (fun j => j) k m) ∈ B k)
    (n : ℕ) (within : n ≤ N) :
    prefixOrbit G (fun j => j) n (κ 0 m) = κ n (prefixOrbit F (fun j => j) n m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have step : n < N := within
    have previous : n ≤ N := Nat.le_of_lt step
    simp only [prefixOrbit, dite_eq_left step]
    rw [ih previous, agreement ⟨n, step⟩ _ (tracking n step)]
    rw [(κ n).left_inv (valid n previous)]

/-- The endpoint equality is a direct consequence of the same literal
cylinder validity, including the zero-length word. -/
theorem endpoint_eq {N : ℕ} (F : Fin N → M → M) (G : Fin N → E → E)
    (κ : ℕ → OpenPartialHomeomorph M E) (B : ℕ → Set E)
    (agreement : ∀ k : Fin N, ∀ z ∈ B k.val,
      G k z = κ (k.val+1) (F k ((κ k.val).symm z)))
    (m : M)
    (valid : ∀ k ≤ N, prefixOrbit F (fun j => j) k m ∈ (κ k).source)
    (tracking : ∀ k < N, κ k (prefixOrbit F (fun j => j) k m) ∈ B k) :
    prefixOrbit G (fun j => j) N (κ 0 m) = κ N (prefixOrbit F (fun j => j) N m) :=
  prefix_eq F G κ B agreement m valid tracking N le_rfl

end LeanShared.PartialChartWordAgreement
