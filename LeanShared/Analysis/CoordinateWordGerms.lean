module
public import LeanShared.Analysis.CoordinateWordIdentity
public import Mathlib.Order.Filter.Finite

/-! Local coordinate-word identities for continuous actual maps. The
neighborhood of validity may depend on the maps and the base point. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology

theorem word_continuous {M : Type*} [TopologicalSpace M]
    (f : ℕ → M → M) (continuous : ∀ n, Continuous (f n)) (N : ℕ) :
    Continuous (word f N) := by
  induction N with
  | zero => exact continuous_id
  | succ n ih => exact (continuous n).comp ih

theorem coordinate_word_germ
    {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]
    (chart : ℕ → OpenPartialHomeomorph M E) (f : ℕ → M → M)
    (continuous : ∀ n, Continuous (f n)) (v : E) (N : ℕ)
    (initial : v ∈ (chart 0).target)
    (inside : ∀ n ≤ N, word f n ((chart 0).symm v) ∈ (chart n).source) :
    word (fun n => chart (n + 1) ∘ f n ∘ (chart n).symm) N =ᶠ[𝓝 v]
      chart N ∘ word f N ∘ (chart 0).symm := by
  have near : ∀ᶠ y in 𝓝 v, ∀ n : Fin (N + 1),
      word f n.val ((chart 0).symm y) ∈ (chart n.val).source := by
    rw [eventually_all]
    intro n
    exact ((word_continuous f continuous n.val).continuousAt.comp
      ((chart 0).continuousAt_symm initial)).eventually
        ((chart n.val).open_source.mem_nhds (inside n.val (Nat.le_of_lt_succ n.isLt)))
  filter_upwards [near, (chart 0).open_target.mem_nhds initial] with y hy hi
  exact coordinate_word_symm_apply chart f y N hi
    (fun n hn => hy ⟨n, Nat.lt_succ_of_le hn⟩)

end LeanShared.FiniteJetComposition
