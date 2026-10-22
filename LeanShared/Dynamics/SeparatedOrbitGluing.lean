module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

/-! Tracing two separated orbit segments preserves the full number of
independent choices. Both seams and their exact time offsets are explicit. -/
public noncomputable section
open Set
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 1200000 in
theorem traced_pair_separation (T : X → X) (K : Set X)
    (s t : Finset X) (n m gap : ℕ) (ε : ℝ)
    (first : Separated T K (n + 1) (3 * ε) s)
    (second : Separated T K (m + 1) (3 * ε) t)
    (trace : {p : X × X // p ∈ s.product t} → X)
    (traceFirst : ∀ p, ∀ j ≤ n, dist (T^[j] (trace p)) (T^[j] p.val.1) < ε)
    (traceSecond : ∀ p, ∀ j ≤ m,
      dist (T^[n + gap + j] (trace p)) (T^[j] p.val.2) < ε) :
    ∀ p q : {p : X × X // p ∈ s.product t}, p ≠ q →
      ∃ j < n + gap + m + 1, ε ≤ dist (T^[j] (trace p)) (T^[j] (trace q)) := by
  classical
  let I := {p : X × X // p ∈ s.product t}
  have separates (p q : I) (different : p ≠ q) :
      ∃ j < n + gap + m + 1, ε ≤ dist (T^[j] (trace p)) (T^[j] (trace q)) := by
    by_cases sameFirst : p.val.1 = q.val.1
    · have differentSecond : p.val.2 ≠ q.val.2 := by
        intro equal
        exact different (Subtype.ext (Prod.ext sameFirst equal))
      obtain ⟨j, hj, apart⟩ := second.2 _ (Finset.mem_product.mp p.property).2
        _ (Finset.mem_product.mp q.property).2 differentSecond
      refine ⟨n + gap + j, by omega, ?_⟩
      have hp := traceSecond p j (by omega)
      have hq := traceSecond q j (by omega)
      have triangle := dist_triangle4 (T^[j] p.val.2) (T^[n + gap + j] (trace p))
        (T^[n + gap + j] (trace q)) (T^[j] q.val.2)
      rw [dist_comm] at hp
      linarith
    · obtain ⟨j, hj, apart⟩ := first.2 _ (Finset.mem_product.mp p.property).1
        _ (Finset.mem_product.mp q.property).1 sameFirst
      refine ⟨j, by omega, ?_⟩
      have hp := traceFirst p j (by omega)
      have hq := traceFirst q j (by omega)
      have triangle := dist_triangle4 (T^[j] p.val.1) (T^[j] (trace p))
        (T^[j] (trace q)) (T^[j] q.val.1)
      rw [dist_comm] at hp
      linarith
  exact separates

set_option maxHeartbeats 1200000 in
theorem separated_traced_pairs (T : X → X) (K : Set X)
    (s t : Finset X) (n m gap : ℕ) (ε : ℝ) (positive : 0 < ε)
    (first : Separated T K (n + 1) (3 * ε) s)
    (second : Separated T K (m + 1) (3 * ε) t)
    (trace : {p : X × X // p ∈ s.product t} → X)
    (member : ∀ p, trace p ∈ K)
    (traceFirst : ∀ p, ∀ j ≤ n, dist (T^[j] (trace p)) (T^[j] p.val.1) < ε)
    (traceSecond : ∀ p, ∀ j ≤ m,
      dist (T^[n + gap + j] (trace p)) (T^[j] p.val.2) < ε) :
    ∃ q : Finset X, Separated T K (n + gap + m + 1) ε q ∧
      q.card = s.card * t.card := by
  classical
  let I := {p : X × X // p ∈ s.product t}
  have separates := traced_pair_separation T K s t n m gap ε first second trace traceFirst traceSecond
  have injective : Function.Injective trace := by
    intro p q equal
    by_contra different
    obtain ⟨j, _, apart⟩ := separates p q different
    rw [equal, dist_self] at apart
    exact (not_le_of_gt positive) apart
  refine ⟨Finset.univ.image trace, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact member p
  · intro x hx y hy different
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
    exact separates p q (fun equal => different (congrArg trace equal))
  · rw [Finset.card_image_of_injective _ injective, Finset.card_univ]
    rw [Fintype.card_coe]
    exact Finset.card_product s t

end LeanShared.ThermodynamicDefinitions
