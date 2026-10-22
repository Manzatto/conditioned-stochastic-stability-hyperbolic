module
public import LeanShared.Analysis.FiniteJetWords
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-! A word of genuine coordinate expressions is the coordinate expression
of the actual word whenever the actual orbit follows the chart itinerary. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set

theorem coordinate_word_apply
    {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]
    (chart : ℕ → OpenPartialHomeomorph M E) (f : ℕ → M → M)
    (x : M) (N : ℕ)
    (inside : ∀ n ≤ N, word f n x ∈ (chart n).source) :
    word (fun n => chart (n + 1) ∘ f n ∘ (chart n).symm) N (chart 0 x) =
      chart N (word f N x) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    change chart (n + 1) (f n ((chart n).symm
      (word (fun j => chart (j + 1) ∘ f j ∘ (chart j).symm) n (chart 0 x)))) = _
    rw [ih (fun j hj => inside j (Nat.le_succ_of_le hj)),
      (chart n).left_inv (inside n (Nat.le_succ n))]
    rfl

theorem coordinate_word_symm_apply
    {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]
    (chart : ℕ → OpenPartialHomeomorph M E) (f : ℕ → M → M)
    (v : E) (N : ℕ) (initial : v ∈ (chart 0).target)
    (inside : ∀ n ≤ N, word f n ((chart 0).symm v) ∈ (chart n).source) :
    word (fun n => chart (n + 1) ∘ f n ∘ (chart n).symm) N v =
      chart N (word f N ((chart 0).symm v)) := by
  simpa only [(chart 0).right_inv initial] using
    coordinate_word_apply chart f ((chart 0).symm v) N inside

end LeanShared.FiniteJetComposition
