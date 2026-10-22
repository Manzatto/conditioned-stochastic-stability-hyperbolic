module
public import LeanShared.Analysis.FiniteJetComposition
import all LeanShared.Analysis.FiniteJetComposition

/-! Finite actual words preserve the moving-point jet convergence supplied
by ordinary local C¹ estimates. The maps and domains may vary with time;
the derivative of a noisy word is derived by the chain rule. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology

@[expose] def word {E : Type*} (f : ℕ → E → E) : ℕ → E → E
  | 0 => id
  | n + 1 => f n ∘ word f n

theorem JetConvergesOn.finite_words
    {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → A → E → E) (g : ℕ → E → E) (l : Filter A) (U : ℕ → Set E)
    (converges : ∀ n, JetConvergesOn (f n) (g n) l (U n))
    (maps : ∀ n, MapsTo (g n) (U n) (U (n + 1))) (N : ℕ) :
    JetConvergesOn (fun a => word (fun n => f n a) N) (word g N) l (U 0) := by
  have result : ∀ n, MapsTo (word g n) (U 0) (U n) ∧
      JetConvergesOn (fun a => word (fun j => f j a) n) (word g n) l (U 0) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ hx => hx, ?_⟩
      unfold JetConvergesOn
      intro x _
      refine ⟨differentiableAt_id, fun v hv => ⟨hv, ?_, ?_⟩⟩
      · simpa only [word, fderiv_id] using
          (tendsto_const_nhds : Tendsto (fun _ : A => ContinuousLinearMap.id ℝ E) l
            (𝓝 (ContinuousLinearMap.id ℝ E)))
      · exact Eventually.of_forall (fun _ => differentiableAt_id)
    | succ n ih =>
      exact ⟨(maps n).comp ih.1, (converges n).comp ih.2 ih.1⟩
  exact (result N).2

end LeanShared.FiniteJetComposition
