module
public import LeanShared.Dynamics.FiniteExpansiveCylinders

/-! Genuine generating open cylinders without restricting their points to
survivors. The base-cover union lies in a compact isolating neighborhood,
as required in Baladi--Tsujii (2008), §3.1. -/
@[expose] public section
open Set Function
namespace LeanShared.GeneratingOpenCylinders
variable {X J : Type*} [MetricSpace X]

/-- BT's integer times [-m,m): backward label j is time -(j+1). -/
def cylinder (T : X ≃ₜ X) (charts : J → Set X) {m : ℕ}
    (forward backward : Fin m → J) : Set X :=
  {x | (∀ j : Fin m, (T : X → X)^[j.val] x ∈ charts (forward j)) ∧
    (∀ j : Fin m, (T.symm : X → X)^[j.val + 1] x ∈ charts (backward j))}

/-- Small charts in the isolating neighborhood genuinely generate in the
unrestricted-cylinder sense, using only compactness and core expansivity. -/
theorem generating (T : X ≃ₜ X) {K : Set X} (hK : IsCompact K)
    (c : ℝ) (charts : J → Set X) (contained : ∀ i, charts i ⊆ K)
    (mesh : ∀ i, ∀ x ∈ charts i, ∀ y ∈ charts i, dist x y ≤ c)
    (expansive : ∀ x ∈ isolatedCore T K, ∀ y ∈ isolatedCore T K,
      (∀ j : ℕ, dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
        dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ m ≥ N, ∀ forward backward : Fin m → J,
      ∀ x ∈ cylinder T charts forward backward,
      ∀ y ∈ cylinder T charts forward backward, dist x y < ε := by
  obtain ⟨n, hn, hsep⟩ := FiniteExpansiveCylinders.exists_finite_separation T hK c expansive ε hε
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  intro m hm forward backward x hx y hy
  apply hsep x y
  intro j hj
  have hjm : j < m := lt_of_lt_of_le (Nat.lt_succ_of_le hj) hm
  let k : Fin m := ⟨j, hjm⟩
  have hxf := hx.1 k
  have hyf := hy.1 k
  refine ⟨contained _ hxf, contained _ hyf, mesh _ _ hxf _ hyf, ?_⟩
  rcases j with _ | j
  · exact ⟨contained _ (hx.1 ⟨0, by omega⟩), contained _ (hy.1 ⟨0, by omega⟩),
      mesh _ _ (hx.1 ⟨0, by omega⟩) _ (hy.1 ⟨0, by omega⟩)⟩
  · have hxb := hx.2 ⟨j, by omega⟩
    have hyb := hy.2 ⟨j, by omega⟩
    exact ⟨contained _ hxb, contained _ hyb, mesh _ _ hxb _ hyb⟩

end LeanShared.GeneratingOpenCylinders
