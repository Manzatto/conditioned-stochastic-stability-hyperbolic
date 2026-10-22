module

public import LeanShared.Dynamics.FiniteExpansiveTube
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

/-! Compact expansivity gives a uniform fine-separated cardinal bound in
every coarse Bowen tube, independently of the observed time horizon. -/
public noncomputable section
open Set Function Metric
namespace LeanShared.FiniteExpansiveWords
variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_uniform_tube_card_bound (T : X ≃ₜ X) (c : ℝ) (hc : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x=y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℕ,
      ∀ n : ℕ, ∀ s : Finset X, ThermodynamicDefinitions.Separated T univ n ε s →
      (∀ x ∈ s, ∀ y ∈ s, ∀ i < n,
        dist ((T : X → X)^[i] x) ((T : X → X)^[i] y) ≤ c) → s.card ≤ C := by
  classical
  obtain ⟨centers,_,finite,cover⟩ := (isCompact_univ : IsCompact (univ : Set X)).finite_cover_balls (half_pos hc)
  let : Fintype centers := finite.fintype
  have nearby (x : X) : ∃ y : centers, dist x y.val < c/2 := by
    obtain ⟨y,hy⟩ := mem_iUnion.mp (cover (mem_univ x))
    obtain ⟨hcenter,hnear⟩ := mem_iUnion.mp hy
    exact ⟨⟨y,hcenter⟩,hnear⟩
  choose label near using nearby
  have mesh (x y : X) (equal : label x=label y) : dist x y ≤ c := by
    have nx := near x
    have ny := near y
    rw [←equal] at ny
    have triangle := dist_triangle x (label x).val y
    rw [dist_comm (label x).val y] at triangle
    linarith
  intro ε hε
  obtain ⟨N,_,detects⟩ := FiniteExpansiveCylinders.exists_finite_separation T
    (isCompact_univ : IsCompact (univ : Set X)) c (fun x _ y _ => expansive x y) ε hε
  refine ⟨(Fintype.card centers) ^ (2 * N), fun n s separated tube => ?_⟩
  have detects' : ∀ x y, (∀ j ≤ N,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → dist x y < ε := by
    intro x y paired
    apply detects x y
    intro j hj
    exact ⟨mem_univ _,mem_univ _,(paired j hj).1,mem_univ _,mem_univ _,(paired j hj).2⟩
  exact separated_tube_card_le T label c ε N mesh detects' n s separated tube

end LeanShared.FiniteExpansiveWords
