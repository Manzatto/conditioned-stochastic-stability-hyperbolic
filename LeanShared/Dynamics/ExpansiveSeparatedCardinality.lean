module

public import LeanShared.Dynamics.FiniteExpansiveWords
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

/-! One fixed finite alphabet bounds separated orbit sets at every finer
scale, with a scale-dependent padding but a scale-independent growth base. -/
public noncomputable section
open Set Function Metric
namespace LeanShared.FiniteExpansiveWords
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

theorem exists_uniform_card_bound (T : X ≃ₜ X) (c : ℝ) (hc : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x=y) :
    ∃ a : ℕ, 0 < a ∧ ∀ ε : ℝ, 0 < ε → ∃ p : ℕ,
      ∀ n : ℕ, ∀ s : Finset X, ThermodynamicDefinitions.Separated T univ n ε s →
        s.card ≤ a^(n+p) := by
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
  have nonempty : Nonempty centers := ⟨label (Classical.arbitrary X)⟩
  let : Nonempty centers := nonempty
  refine ⟨Fintype.card centers,Fintype.card_pos,?_⟩
  intro ε hε
  obtain ⟨N,_,detects⟩ := FiniteExpansiveCylinders.exists_finite_separation T
    (isCompact_univ : IsCompact (univ : Set X)) c (fun x _ y _ => expansive x y) ε hε
  refine ⟨2*N+1,fun n s separated => ?_⟩
  have detects' : ∀ x y, (∀ j ≤ N,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → dist x y < ε := by
    intro x y paired
    apply detects x y
    intro j hj
    exact ⟨mem_univ _,mem_univ _,(paired j hj).1,mem_univ _,mem_univ _,(paired j hj).2⟩
  simpa only [Nat.add_assoc] using separated_card_le T label c ε N mesh detects' n s separated

end LeanShared.FiniteExpansiveWords
