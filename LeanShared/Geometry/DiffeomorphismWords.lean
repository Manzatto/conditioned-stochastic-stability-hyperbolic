module
public import LeanShared.Analysis.FiniteJetWords
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! Chronological finite words of genuine C1 diffeomorphisms are genuine
C1 diffeomorphisms, with the literal word function and the actual inverse. -/
public noncomputable section
open scoped Manifold
namespace LeanShared.DiffeomorphismWords
variable {M : Type*} [TopologicalSpace M]

@[expose] def homeomorph (H : ℕ → M ≃ₜ M) : ℕ → M ≃ₜ M
  | 0 => Homeomorph.refl M
  | n+1 => (homeomorph H n).trans (H n)

theorem coe_word (H : ℕ → M ≃ₜ M) (n : ℕ) :
    (homeomorph H n : M → M) = FiniteJetComposition.word (fun j => (H j : M → M)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    exact congrArg (H n) (congrFun ih x)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M]

theorem forward (H : ℕ → M ≃ₜ M)
    (smooth : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (H j)) (n : ℕ) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (homeomorph H n) := by
  induction n with
  | zero => exact contMDiff_id
  | succ n ih => exact (smooth n).comp ih

theorem backward (H : ℕ → M ≃ₜ M)
    (smooth : ∀ j, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (H j).symm) (n : ℕ) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (homeomorph H n).symm := by
  induction n with
  | zero => exact contMDiff_id
  | succ n ih => exact ih.comp (smooth n)

end LeanShared.DiffeomorphismWords
