module
public import LeanShared.Analysis.FiniteJetWords
import all LeanShared.Analysis.FiniteJetComposition

/-! Finite words need only follow the chosen deterministic itinerary. No
forward invariance of individual coordinate neighborhoods is required. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology

theorem JetConvergesOn.finite_words_of_itinerary
    {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → A → E → E) (g : ℕ → E → E) (l : Filter A)
    (U : Set E) (V : ℕ → Set E) (N : ℕ)
    (converges : ∀ n < N, JetConvergesOn (f n) (g n) l (V n))
    (itinerary : ∀ n < N, MapsTo (word g n) U (V n)) :
    JetConvergesOn (fun a => word (fun n => f n a) N) (word g N) l U := by
  have result : ∀ n ≤ N,
      JetConvergesOn (fun a => word (fun j => f j a) n) (word g n) l U := by
    intro n hn
    induction n with
    | zero =>
      unfold JetConvergesOn
      intro x _
      refine ⟨differentiableAt_id, fun v hv => ⟨hv, ?_, ?_⟩⟩
      · simpa only [word, fderiv_id] using
          (tendsto_const_nhds : Tendsto (fun _ : A => ContinuousLinearMap.id ℝ E) l
            (𝓝 (ContinuousLinearMap.id ℝ E)))
      · exact Eventually.of_forall (fun _ => differentiableAt_id)
    | succ n ih =>
      exact (converges n (Nat.lt_of_succ_le hn)).comp
        (ih (Nat.le_of_succ_le hn)) (itinerary n (Nat.lt_of_succ_le hn))
  exact result N le_rfl

end LeanShared.FiniteJetComposition
