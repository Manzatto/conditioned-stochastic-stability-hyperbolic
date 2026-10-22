module

public import LeanShared.Dynamics.MarkovNoDiamonds
public import LeanShared.Dynamics.FiniteEndpointCoding
public import LeanShared.Dynamics.MarkovItineraryCoding

/-! Uniform finite fibers for the coding defined by closed finite raw
Markov itineraries.  No injectivity of boundary labels is used: actual
expansivity proves finite-window no-diamonds, and endpoint pairs supply
the uniform cardinal bound.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding ExpansiveLocalProduct
open scoped Topology
variable {X I : Type*} [MetricSpace X] [TopologicalSpace I]

omit [TopologicalSpace I] in
theorem closed_window_coordinate (T : X ≃ₜ X) (rectangles : I → Set X) (word : ℤ → I)
    (radius : ℕ) (x : X) (inside : x ∈ closure (itineraryWindow T rectangles word radius))
    (k : ℤ) (lower : -(radius : ℤ) ≤ k) (upper : k ≤ radius) :
    (T ^ k) x ∈ closure (rectangles (word k)) := by
  have closed : IsClosed ((T ^ k) ⁻¹' closure (rectangles (word k))) :=
    isClosed_closure.preimage (T ^ k).continuous
  have subset : itineraryWindow T rectangles word radius ⊆ (T ^ k) ⁻¹' closure (rectangles (word k)) := by
    intro y hy
    exact subset_closure (hy k lower upper)
  exact (closed.closure_subset_iff.mpr subset) inside

variable (T : X ≃ₜ X) (rectangles : I → Set X) (δ : ℝ)
    (forward : ∀ i j x y, x ∈ rectangles i → y ∈ rectangles i → T x ∈ rectangles j →
      (∀ n : ℕ, dist ((T : X → X)^[n] y) ((T : X → X)^[n] x) ≤ δ) →
      T y ∈ rectangles j ∧
        ∀ n : ℕ, dist ((T : X → X)^[n] (T y)) ((T : X → X)^[n] (T x)) ≤ δ)
    (inverse : ∀ i j x y, x ∈ rectangles i → y ∈ rectangles i → T.symm x ∈ rectangles j →
      (∀ n : ℕ, dist ((T.symm : X → X)^[n] y) ((T.symm : X → X)^[n] x) ≤ δ) →
      T.symm y ∈ rectangles j ∧
        ∀ n : ℕ, dist ((T.symm : X → X)^[n] (T.symm y))
          ((T.symm : X → X)^[n] (T.symm x)) ≤ δ)
    (c : ℝ)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c)
    (disjoint : Pairwise (fun i j => Disjoint (rectangles i) (rectangles j)))
    (diameter : ∀ i, ∀ x ∈ rectangles i, ∀ y ∈ rectangles i, dist x y ≤ δ)
    (product : ∀ i x y, x ∈ rectangles i → y ∈ rectangles i →
      ∃ z ∈ rectangles i, ProductRelation T δ x y z)
    (code : Path (Transition T rectangles) → X)
    (windows : ∀ a radius, code a ∈ closure (itineraryWindow T rectangles a.val radius))
include forward inverse expansive small disjoint diameter product windows

omit [TopologicalSpace I] in
theorem coding_no_diamonds (a b : Path (Transition T rectangles)) (samePoint : code a = code b)
    (radius : ℕ) (sameStart : a.val (-(radius : ℤ)) = b.val (-(radius : ℤ)))
    (sameEnd : a.val radius = b.val radius) :
    ∀ k : ℤ, -(radius : ℤ) ≤ k → k ≤ radius → a.val k = b.val k := by
  let wordA : ℕ → I := fun j => a.val ((j : ℤ) - radius)
  let wordB : ℕ → I := fun j => b.val ((j : ℤ) - radius)
  have realized (p : Path (Transition T rectangles)) :
      ∃ x : X, ∀ j ≤ 2 * radius, (T : X → X)^[j] x ∈ rectangles (p.val ((j : ℤ) - radius)) := by
    have initial : (rectangles (p.val ((0 : ℤ) - radius))).Nonempty := by
      obtain ⟨x, inside, _⟩ := p.property (-(radius : ℤ))
      exact ⟨x, by simpa only [zero_sub] using inside⟩
    apply finite_path_realized T rectangles δ inverse forward product (fun j => p.val ((j : ℤ) - radius))
      (2 * radius) initial
    intro j _
    have index : ((j + 1 : ℕ) : ℤ) - radius = ((j : ℤ) - radius) + 1 := by omega
    simpa only [index] using p.property ((j : ℤ) - radius)
  obtain ⟨xA, itineraryA⟩ := realized a
  obtain ⟨xB, itineraryB⟩ := realized b
  have initialEqual : wordA 0 = wordB 0 := by
    simpa only [wordA, wordB, Nat.cast_zero, zero_sub] using sameStart
  have endEqual : wordA (2 * radius) = wordB (2 * radius) := by
    have index : ((2 * radius : ℕ) : ℤ) - radius = (radius : ℤ) := by omega
    simpa only [wordA, wordB, index] using sameEnd
  have commonA (j : ℕ) (bound : j ≤ 2 * radius) :
      (T ^ ((j : ℤ) - radius)) (code a) ∈ closure (rectangles (wordA j)) :=
    closed_window_coordinate T rectangles a.val radius (code a) (windows a radius)
      ((j : ℤ) - radius) (by omega) (by omega)
  have commonB (j : ℕ) (bound : j ≤ 2 * radius) :
      (T ^ ((j : ℤ) - radius)) (code a) ∈ closure (rectangles (wordB j)) := by
    rw [samePoint]
    exact closed_window_coordinate T rectangles b.val radius (code b) (windows b radius)
      ((j : ℤ) - radius) (by omega) (by omega)
  have result := no_diamonds T rectangles δ forward inverse c expansive small disjoint diameter product
    wordA wordB (2 * radius) initialEqual endEqual xA xB itineraryA itineraryB
    (fun j => (T ^ ((j : ℤ) - radius)) (code a)) commonA commonB
  intro k lower upper
  let j := (k + radius).toNat
  have index : (j : ℤ) = k + radius := Int.toNat_of_nonneg (by omega)
  have bound : j ≤ 2 * radius := by omega
  have equal := result j bound
  simpa only [wordA, wordB, index, add_sub_cancel_right] using equal

omit [TopologicalSpace I] in
/-- Every coding fiber is finite and has at most the square of the
number of raw partition atoms. -/
theorem coding_fiber_finite_card [Fintype I] (x : X) :
    (code ⁻¹' {x}).Finite ∧ (code ⁻¹' {x}).ncard ≤ (Fintype.card I) ^ 2 := by
  apply FiniteEndpointCoding.finite_card_bound (fun a : Path (Transition T rectangles) => a.val)
    (fun a b h => Subtype.ext h)
  intro a ha b hb radius sameStart sameEnd
  have samePoint : code a = code b := (show code a = x from ha).trans (show code b = x from hb).symm
  exact coding_no_diamonds T rectangles δ forward inverse c expansive small disjoint diameter product
    code windows a b samePoint radius sameStart sameEnd

end LeanShared.MarkovFinitePathRealization
