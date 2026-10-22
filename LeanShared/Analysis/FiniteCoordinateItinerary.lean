module
public import LeanShared.Analysis.FiniteJetItinerary
import all LeanShared.Analysis.FiniteJetComposition

/-! The valid initial domain of a finite coordinate itinerary is constructed
from the actual deterministic maps. Its openness and the continuity of all
valid partial words follow from local continuity on the coordinate domains. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology

@[expose] def prefixDomain {E : Type*} (g : ℕ → E → E) (V : ℕ → Set E) : ℕ → Set E
  | 0 => univ
  | n + 1 => prefixDomain g V n ∩ word g n ⁻¹' V n

theorem prefixDomain_mono {E : Type*} (g : ℕ → E → E) (V : ℕ → Set E)
    {n N : ℕ} (hn : n ≤ N) : prefixDomain g V N ⊆ prefixDomain g V n := by
  induction N with
  | zero =>
    have same : n = 0 := Nat.le_zero.mp hn
    subst n
    exact Subset.rfl
  | succ N ih =>
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · exact Subset.rfl
    · exact (ih (Nat.le_of_lt_succ hlt)).trans' inter_subset_left

theorem prefixDomain_itinerary {E : Type*} (g : ℕ → E → E) (V : ℕ → Set E)
    {n N : ℕ} (hn : n < N) : MapsTo (word g n) (prefixDomain g V N) (V n) := by
  intro x hx
  exact (prefixDomain_mono g V (Nat.succ_le_of_lt hn) hx).2

theorem prefixDomain_open_and_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℕ → E → E) (V : ℕ → Set E)
    (openV : ∀ n, IsOpen (V n)) (continuous : ∀ n, ContinuousOn (g n) (V n)) (N : ℕ) :
    IsOpen (prefixDomain g V N) ∧ ContinuousOn (word g N) (prefixDomain g V N) := by
  induction N with
  | zero => exact ⟨isOpen_univ, continuousOn_id⟩
  | succ n ih =>
    refine ⟨ih.2.isOpen_inter_preimage ih.1 (openV n), ?_⟩
    exact (continuous n).comp (ih.2.mono inter_subset_left) (fun _ hx => hx.2)

theorem JetConvergesOn.finite_coordinate_itinerary
    {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → A → E → E) (g : ℕ → E → E) (l : Filter A)
    (V : ℕ → Set E) (N : ℕ)
    (converges : ∀ n < N, JetConvergesOn (f n) (g n) l (V n)) :
    JetConvergesOn (fun a => word (fun n => f n a) N) (word g N) l (prefixDomain g V N) :=
  JetConvergesOn.finite_words_of_itinerary f g l _ V N converges
    (fun _ hn => prefixDomain_itinerary g V hn)

end LeanShared.FiniteJetComposition
