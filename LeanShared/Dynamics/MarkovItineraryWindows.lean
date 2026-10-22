module

public import LeanShared.Dynamics.MarkovFinitePathRealization

/-! Nonempty nested closed itinerary windows for the actual transition
graph.  The closures retain whole finite orbit itineraries, rather than
only separate memberships in closures of individual rectangles.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding
open scoped Topology
variable {X I : Type*} [MetricSpace X]

/-- A centered finite orbit itinerary using integer homeomorphism powers. -/
@[expose] def itineraryWindow (T : X ≃ₜ X) (rectangles : I → Set X)
    (word : ℤ → I) (radius : ℕ) : Set X :=
  {x | ∀ k : ℤ, -(radius : ℤ) ≤ k → k ≤ radius → (T ^ k) x ∈ rectangles (word k)}

theorem pow_apply_time_shift (T : X ≃ₜ X) (x : X) (k l : ℤ) :
    (T ^ k) ((T ^ l) x) = (T ^ (k + l)) x := by
  rw [zpow_add]
  rfl

/-- Realization of ordinary finite paths gives every centered window. -/
theorem itineraryWindow_nonempty [TopologicalSpace I]
    (T : X ≃ₜ X) (rectangles : I → Set X)
    (realized : ∀ word : ℕ → I, ∀ length : ℕ, (rectangles (word 0)).Nonempty →
      (∀ k < length, Transition T rectangles (word k) (word (k + 1))) →
      ∃ x : X, ∀ k ≤ length, (T : X → X)^[k] x ∈ rectangles (word k))
    (a : Path (Transition T rectangles)) (radius : ℕ) :
    (itineraryWindow T rectangles a.val radius).Nonempty := by
  let word : ℕ → I := fun j => a.val ((j : ℤ) - radius)
  have initial : (rectangles (word 0)).Nonempty := by
    obtain ⟨x, hx, _⟩ := a.property (-(radius : ℤ))
    exact ⟨x, by simpa only [word, Nat.cast_zero, zero_sub] using hx⟩
  have edges (j : ℕ) (_ : j < 2 * radius) : Transition T rectangles (word j) (word (j + 1)) := by
    have index : ((j + 1 : ℕ) : ℤ) - radius = ((j : ℤ) - radius) + 1 := by omega
    simpa only [word, index] using a.property ((j : ℤ) - radius)
  obtain ⟨y, itinerary⟩ := realized word (2 * radius) initial edges
  refine ⟨(T ^ (radius : ℤ)) y, ?_⟩
  intro k lower upper
  let j : ℕ := (k + radius).toNat
  have index : (j : ℤ) = k + radius := Int.toNat_of_nonneg (by omega)
  have bound : j ≤ 2 * radius := by omega
  have label : word j = a.val k := by
    change a.val ((j : ℤ) - radius) = a.val k
    rw [index, add_sub_cancel_right]
  have time : (T ^ k) ((T ^ (radius : ℤ)) y) = (T : X → X)^[j] y := by
    rw [pow_apply_time_shift, ← index, zpow_natCast, DiffeomorphismIterates.coe_pow]
  rw [time, ← label]
  exact itinerary j bound

theorem itineraryWindow_antitone (T : X ≃ₜ X) (rectangles : I → Set X) (word : ℤ → I) :
    Antitone (itineraryWindow T rectangles word) := by
  intro m n le x hx k lower upper
  exact hx k (by omega) (by omega)

/-- Compactness produces a point in the closures of every exact finite
itinerary cylinder for a fixed infinite path. -/
theorem closed_itinerary_windows_nonempty [TopologicalSpace I] [CompactSpace X]
    (T : X ≃ₜ X) (rectangles : I → Set X)
    (realized : ∀ word : ℕ → I, ∀ length : ℕ, (rectangles (word 0)).Nonempty →
      (∀ k < length, Transition T rectangles (word k) (word (k + 1))) →
      ∃ x : X, ∀ k ≤ length, (T : X → X)^[k] x ∈ rectangles (word k))
    (a : Path (Transition T rectangles)) :
    (⋂ radius : ℕ, closure (itineraryWindow T rectangles a.val radius)).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun radius => closure (itineraryWindow T rectangles a.val radius))
  · exact fun n => closure_mono (itineraryWindow_antitone T rectangles a.val (Nat.le_succ n))
  · exact fun n => (itineraryWindow_nonempty T rectangles realized a n).closure
  · exact isClosed_closure.isCompact
  · exact fun _ => isClosed_closure

/-- A point in all closed finite windows shadows the chosen rectangle
centers, with the original quantitative rectangle bound. -/
theorem closed_windows_near (T : X ≃ₜ X) (rectangles : I → Set X) (center : I → X) (ε : ℝ)
    (near : ∀ i, ∀ x ∈ rectangles i, dist x (center i) ≤ ε)
    (word : ℤ → I) (x : X)
    (inside : ∀ radius : ℕ, x ∈ closure (itineraryWindow T rectangles word radius)) (n : ℤ) :
    dist (BilateralHomeomorphismOrbit.orbit T x n) (center (word (-n))) ≤ ε := by
  let radius := n.natAbs
  have closed : IsClosed {x : X |
      dist (BilateralHomeomorphismOrbit.orbit T x n) (center (word (-n))) ≤ ε} :=
    isClosed_le ((T ^ (-n)).continuous.dist continuous_const) continuous_const
  have subset : itineraryWindow T rectangles word radius ⊆
      {x : X | dist (BilateralHomeomorphismOrbit.orbit T x n) (center (word (-n))) ≤ ε} := by
    intro y hy
    exact near (word (-n)) _ (hy (-n) (by omega) (by omega))
  exact (closed.closure_subset_iff.mpr subset) (inside radius)

end LeanShared.MarkovFinitePathRealization
