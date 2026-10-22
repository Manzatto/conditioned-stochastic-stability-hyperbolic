module

public import LeanShared.Dynamics.MarkovItineraryWindows

/-! A continuous surjective coding for a finite Markov refinement is
constructed from closures of realized finite itinerary cylinders.  The
whole finite-cylinder provenance is retained for the multiplicity proof.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding BilateralHomeomorphismOrbit
open scoped Topology
variable {X I : Type*} [MetricSpace X] [TopologicalSpace I]

omit [TopologicalSpace I] in
/-- Every orbit has an admissible itinerary in a covering transition graph. -/
theorem exists_orbit_itinerary (T : X ≃ₜ X) (rectangles : I → Set X)
    (cover : (⋃ i, rectangles i) = univ) (x : X) :
    ∃ a : Path (Transition T rectangles), ∀ k : ℤ, (T ^ k) x ∈ rectangles (a.val k) := by
  have label (k : ℤ) : ∃ i : I, (T ^ k) x ∈ rectangles i := by
    have inside : (T ^ k) x ∈ ⋃ i, rectangles i := cover.symm ▸ mem_univ _
    exact mem_iUnion.mp inside
  choose word inside using label
  have edges (k : ℤ) : Transition T rectangles (word k) (word (k + 1)) := by
    have step : T ((T ^ k) x) = (T ^ (k + 1)) x := by
      simpa only [zpow_one, add_comm] using pow_apply_time_shift T x 1 k
    exact ⟨(T ^ k) x, inside k, step.symm ▸ inside (k + 1)⟩
  exact ⟨⟨word, edges⟩, inside⟩

/-- The refined graph coding retains every closed finite itinerary
cylinder, in addition to continuity, surjectivity and semiconjugacy. -/
theorem exists_itinerary_coding [DiscreteTopology I] [CompactSpace X]
    (T : X ≃ₜ X) (rectangles : I → Set X) (center : I → X) (c ε : ℝ)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 2 * ε ≤ c)
    (cover : (⋃ i, rectangles i) = univ)
    (near : ∀ i, ∀ x ∈ rectangles i, dist x (center i) ≤ ε)
    (realized : ∀ word : ℕ → I, ∀ length : ℕ, (rectangles (word 0)).Nonempty →
      (∀ k < length, Transition T rectangles (word k) (word (k + 1))) →
      ∃ x : X, ∀ k ≤ length, (T : X → X)^[k] x ∈ rectangles (word k)) :
    ∃ code : Path (Transition T rectangles) → X,
      Continuous code ∧ Surjective code ∧
      (∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε) ∧
      (∀ a, code (shift (Transition T rectangles) a) = T (code a)) ∧
      ∀ a radius, code a ∈ closure (itineraryWindow T rectangles a.val radius) := by
  have selection (a : Path (Transition T rectangles)) :
      ∃ x : X, ∀ radius : ℕ, x ∈ closure (itineraryWindow T rectangles a.val radius) := by
    obtain ⟨x, hx⟩ := closed_itinerary_windows_nonempty T rectangles realized a
    exact ⟨x, fun radius => mem_iInter.mp hx radius⟩
  choose candidate inside using selection
  have candidateNear (a : Path (Transition T rectangles)) (n : ℤ) :
      dist (orbit T (candidate a) n) (center (a.val (-n))) ≤ ε :=
    closed_windows_near T rectangles center ε near a.val (candidate a) (inside a) n
  obtain ⟨code, continuousCode, nearCode, intertwines⟩ :=
    exists_continuous_coding T (Transition T rectangles) center c ε expansive small
      (fun a => ⟨candidate a, candidateNear a⟩)
  have onto : Surjective code := by
    intro x
    obtain ⟨a, itinerary⟩ := exists_orbit_itinerary T rectangles cover x
    refine ⟨a, shadow_unique T c ε expansive small (fun n => center (a.val (-n)))
      (code a) x (nearCode a) ?_⟩
    intro n
    exact near (a.val (-n)) ((T ^ (-n)) x) (itinerary (-n))
  refine ⟨code, continuousCode, onto, nearCode, intertwines, ?_⟩
  intro a radius
  have equal : code a = candidate a := shadow_unique T c ε expansive small
    (fun n => center (a.val (-n))) (code a) (candidate a) (nearCode a) (candidateNear a)
  exact equal.symm ▸ inside a radius

end LeanShared.MarkovFinitePathRealization
