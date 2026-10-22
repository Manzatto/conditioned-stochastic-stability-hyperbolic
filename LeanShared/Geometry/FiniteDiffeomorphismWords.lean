module
public import LeanShared.Geometry.DiffeomorphismWords
public import LeanShared.Analysis.CylinderPrincipalCoefficient

/-! The finite-prefix cylinder convention and the chronological manifold-diffeomorphism word
convention give exactly the same actual map. -/
public noncomputable section
open scoped Manifold
namespace LeanShared.FiniteDiffeomorphismWords
open CylinderPrincipalCoefficient
variable {M : Type*} [TopologicalSpace M]

@[expose] def extend {N : ℕ} (H : Fin N → M ≃ₜ M) (k : ℕ) : M ≃ₜ M :=
  if hk : k<N then H ⟨k,hk⟩ else Homeomorph.refl M

theorem coe_word {N : ℕ} (H : Fin N → M ≃ₜ M) (n : ℕ) :
    (DiffeomorphismWords.homeomorph (extend H) n : M → M) =
      prefixOrbit (fun j : Fin N => (H j : M → M)) (fun j => j) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    by_cases hn : n<N
    · change extend H n (DiffeomorphismWords.homeomorph (extend H) n x) = _
      rw [congrFun ih x]
      simp only [extend,prefixOrbit,dite_eq_left hn]
    · change extend H n (DiffeomorphismWords.homeomorph (extend H) n x) = _
      rw [congrFun ih x]
      simp only [extend,prefixOrbit,dite_eq_right hn,Homeomorph.refl_apply,id_eq]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M]

theorem forward {N : ℕ} (H : Fin N → M ≃ₜ M)
    (smooth : ∀ k, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (H k)) (n : ℕ) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (DiffeomorphismWords.homeomorph (extend H) n) := by
  apply DiffeomorphismWords.forward
  intro k
  by_cases hk : k<N
  · simpa only [extend,dite_eq_left hk] using smooth ⟨k,hk⟩
  · rw [extend,dite_eq_right hk]
    change ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (id : M → M)
    exact contMDiff_id

theorem backward {N : ℕ} (H : Fin N → M ≃ₜ M)
    (smooth : ∀ k, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (H k).symm) (n : ℕ) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (DiffeomorphismWords.homeomorph (extend H) n).symm := by
  apply DiffeomorphismWords.backward
  intro k
  by_cases hk : k<N
  · simpa only [extend,dite_eq_left hk] using smooth ⟨k,hk⟩
  · rw [extend,dite_eq_right hk]
    change ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (id : M → M)
    exact contMDiff_id

end LeanShared.FiniteDiffeomorphismWords
