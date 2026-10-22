module

public import LeanShared.Dynamics.MarkovFinitePathRealization

/-! Small disjoint raw Markov rectangles have no distinct finite
itineraries with the same endpoint rectangles and a common limiting
orbit.  Products at the two endpoints have the same global past/future;
in the middle their distance is controlled by the rectangle diameters.
Actual expansivity identifies them before raw-atom disjointness is used.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function ExpansiveLocalProduct
variable {X I : Type*} [MetricSpace X]

theorem diameter_bound_closure (S : Set X) (δ : ℝ)
    (diameter : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ) (x : X) (hx : x ∈ S) (q : X)
    (hq : q ∈ closure S) : dist x q ≤ δ := by
  have closed : IsClosed {y : X | dist x y ≤ δ} :=
    isClosed_le (continuous_const.dist continuous_id) continuous_const
  exact (closed.closure_subset_iff.mpr (fun y hy => diameter x hx y hy)) hq

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

include forward in
/-- A stable slice follows a finite itinerary, retaining its global
future bound at every intermediate time. -/
theorem stable_follows_prefix (word : ℕ → I) (points : ℕ → X)
    (coherent : ∀ n, T (points n) = points (n + 1)) (length : ℕ)
    (inside : ∀ k ≤ length, points k ∈ rectangles (word k)) (v : X)
    (insideV : v ∈ rectangles (word 0))
    (stable : ∀ n : ℕ, dist ((T : X → X)^[n] v) ((T : X → X)^[n] (points 0)) ≤ δ) :
    ∀ k ≤ length, (T : X → X)^[k] v ∈ rectangles (word k) ∧
      ∀ n : ℕ, dist ((T : X → X)^[n] ((T : X → X)^[k] v))
        ((T : X → X)^[n] (points k)) ≤ δ := by
  intro k hk
  induction k with
  | zero => exact ⟨insideV, stable⟩
  | succ k ih =>
    obtain ⟨insideK, future⟩ := ih (by omega)
    have result := forward (word k) (word (k + 1)) (points k) ((T : X → X)^[k] v)
      (inside k (by omega)) insideK ((coherent k).symm ▸ inside (k + 1) hk) future
    simpa only [iterate_succ_apply', coherent k] using result

include inverse in
/-- Pull an unstable slice through a finite itinerary, retaining its
global past bound at the initial time. -/
theorem unstable_lift_prefix_with_bound (word : ℕ → I) (points : ℕ → X)
    (coherent : ∀ n, T (points n) = points (n + 1)) (length : ℕ)
    (inside : ∀ k ≤ length, points k ∈ rectangles (word k)) (w : X)
    (insideW : w ∈ rectangles (word length))
    (unstable : ∀ n : ℕ,
      dist ((T.symm : X → X)^[n] w) ((T.symm : X → X)^[n] (points length)) ≤ δ) :
    ∃ v : X, (T : X → X)^[length] v = w ∧
      (∀ k ≤ length, (T : X → X)^[k] v ∈ rectangles (word k)) ∧
      ∀ n : ℕ, dist ((T.symm : X → X)^[n] v) ((T.symm : X → X)^[n] (points 0)) ≤ δ := by
  induction length generalizing w with
  | zero => exact ⟨w, rfl, (fun k hk => by simpa only [Nat.eq_zero_of_le_zero hk, iterate_zero_apply] using insideW), unstable⟩
  | succ length ih =>
    have previous : T.symm (points (length + 1)) = points length := by
      rw [← coherent length, T.symm_apply_apply]
    have pulled := inverse (word (length + 1)) (word length) (points (length + 1)) w
      (inside _ le_rfl) insideW (previous.symm ▸ inside length (by omega)) unstable
    have past : ∀ n : ℕ, dist ((T.symm : X → X)^[n] (T.symm w))
        ((T.symm : X → X)^[n] (points length)) ≤ δ := by
      simpa only [previous] using pulled.2
    obtain ⟨v, image, itinerary, initialPast⟩ :=
      ih (fun k hk => inside k (by omega)) (T.symm w) pulled.1 past
    refine ⟨v, ?_, (fun k hk => ?_), initialPast⟩
    · rw [iterate_succ_apply', image, T.apply_symm_apply]
    · by_cases smaller : k ≤ length
      · exact itinerary k smaller
      · have equal : k = length + 1 := by omega
        subst k
        rw [iterate_succ_apply', image, T.apply_symm_apply]
        exact insideW

include forward inverse in
/-- No distinct finite raw Markov itineraries can have the same endpoint
rectangles and a common orbit in all their rectangle closures. -/
theorem no_diamonds (c : ℝ)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c)
    (disjoint : Pairwise (fun i j => Disjoint (rectangles i) (rectangles j)))
    (diameter : ∀ i, ∀ x ∈ rectangles i, ∀ y ∈ rectangles i, dist x y ≤ δ)
    (product : ∀ i x y, x ∈ rectangles i → y ∈ rectangles i →
      ∃ z ∈ rectangles i, ProductRelation T δ x y z)
    (wordA wordB : ℕ → I) (length : ℕ) (sameStart : wordA 0 = wordB 0)
    (sameEnd : wordA length = wordB length) (a b : X)
    (itineraryA : ∀ k ≤ length, (T : X → X)^[k] a ∈ rectangles (wordA k))
    (itineraryB : ∀ k ≤ length, (T : X → X)^[k] b ∈ rectangles (wordB k))
    (q : ℕ → X)
    (commonA : ∀ k ≤ length, q k ∈ closure (rectangles (wordA k)))
    (commonB : ∀ k ≤ length, q k ∈ closure (rectangles (wordB k))) :
    ∀ k ≤ length, wordA k = wordB k := by
  have insideA : a ∈ rectangles (wordA 0) := itineraryA 0 (by omega)
  have insideB : b ∈ rectangles (wordA 0) := sameStart.symm ▸ itineraryB 0 (by omega)
  obtain ⟨leftProduct, insideLeft, leftBounds⟩ := product (wordA 0) a b insideA insideB
  have followsA := stable_follows_prefix T rectangles δ forward wordA
    (fun k => (T : X → X)^[k] a) (fun k => (iterate_succ_apply' _ _ _).symm)
    length itineraryA leftProduct insideLeft (fun n => (leftBounds n).1)
  have insideEndA := itineraryA length le_rfl
  have insideEndB : (T : X → X)^[length] b ∈ rectangles (wordA length) :=
    sameEnd.symm ▸ itineraryB length le_rfl
  obtain ⟨rightProduct, insideRight, rightBounds⟩ := product (wordA length)
    ((T : X → X)^[length] a) ((T : X → X)^[length] b) insideEndA insideEndB
  have insideRightB : rightProduct ∈ rectangles (wordB length) := sameEnd ▸ insideRight
  obtain ⟨rightInitial, imageRight, followsB, pastRight⟩ := unstable_lift_prefix_with_bound T rectangles δ inverse
    wordB (fun k => (T : X → X)^[k] b) (fun k => (iterate_succ_apply' _ _ _).symm)
    length itineraryB rightProduct insideRightB (fun n => (rightBounds n).2)
  have equal : leftProduct = rightInitial := by
    apply expansive
    intro n
    constructor
    · by_cases middle : n ≤ length
      · have boundA := diameter_bound_closure (rectangles (wordA n)) δ (diameter (wordA n))
          _ (followsA n middle).1 (q n) (commonA n middle)
        have boundB := diameter_bound_closure (rectangles (wordB n)) δ (diameter (wordB n))
          _ (followsB n middle) (q n) (commonB n middle)
        have triangle := dist_triangle ((T : X → X)^[n] leftProduct) (q n) ((T : X → X)^[n] rightInitial)
        rw [dist_comm (q n)] at triangle
        linarith
      · let j := n - length
        have times : j + length = n := Nat.sub_add_cancel (by omega)
        have stableLeft := (followsA length le_rfl).2 j
        have stableRight := (rightBounds j).1
        rw [← imageRight] at stableRight
        simp only [← iterate_add_apply, times] at stableLeft stableRight
        have triangle := dist_triangle ((T : X → X)^[j] ((T : X → X)^[length] leftProduct))
          ((T : X → X)^[j] ((T : X → X)^[length] a)) ((T : X → X)^[j] rightProduct)
        rw [dist_comm ((T : X → X)^[j] ((T : X → X)^[length] a))] at triangle
        rw [← imageRight, ← iterate_add_apply, ← iterate_add_apply, ← iterate_add_apply, times] at triangle
        linarith
    · have triangle := dist_triangle ((T.symm : X → X)^[n] leftProduct)
        ((T.symm : X → X)^[n] b) ((T.symm : X → X)^[n] rightInitial)
      have leftPast := (leftBounds n).2
      have rightPast := pastRight n
      rw [iterate_zero_apply] at rightPast
      rw [dist_comm ((T.symm : X → X)^[n] b)] at triangle
      linarith
  intro k hk
  by_contra different
  have membership := (followsA k hk).1
  rw [equal] at membership
  exact Set.disjoint_left.mp (disjoint different) membership (followsB k hk)

end LeanShared.MarkovFinitePathRealization
