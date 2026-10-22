module

public import LeanShared.Dynamics.MarkovCodingFiniteFibers

/-! Matching symbolic windows give actual finite orbit closeness for
closed-itinerary codings.  The rectangle diameter estimate extends to
both closure points by continuity of distance on the product.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding
variable {X I : Type*} [MetricSpace X]

theorem diameter_bound_both_closure (S : Set X) (δ : ℝ)
    (diameter : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ)
    (x y : X) (hx : x ∈ closure S) (hy : y ∈ closure S) : dist x y ≤ δ := by
  have closed : IsClosed {p : X × X | dist p.1 p.2 ≤ δ} :=
    isClosed_le (continuous_fst.dist continuous_snd) continuous_const
  have subset : S ×ˢ S ⊆ {p : X × X | dist p.1 p.2 ≤ δ} :=
    fun p hp => diameter p.1 hp.1 p.2 hp.2
  have inside : (x, y) ∈ closure (S ×ˢ S) := by
    rw [closure_prod_eq]
    exact ⟨hx, hy⟩
  exact (closed.closure_subset_iff.mpr subset) inside

/-- Agreement of symbols on a whole window controls the corresponding
actual orbit points, including boundary-coded points. -/
theorem coding_matching_window_close (T : X ≃ₜ X) (rectangles : I → Set X) (δ : ℝ)
    (diameter : ∀ i, ∀ x ∈ rectangles i, ∀ y ∈ rectangles i, dist x y ≤ δ)
    (code : Path (Transition T rectangles) → X)
    (windows : ∀ a radius, code a ∈ closure (itineraryWindow T rectangles a.val radius))
    (a b : Path (Transition T rectangles)) (radius : ℕ)
    (matching : ∀ k : ℤ, -(radius : ℤ) ≤ k → k ≤ radius → a.val k = b.val k)
    (k : ℤ) (lower : -(radius : ℤ) ≤ k) (upper : k ≤ radius) :
    dist ((T ^ k) (code a)) ((T ^ k) (code b)) ≤ δ := by
  have first := closed_window_coordinate T rectangles a.val radius (code a) (windows a radius) k lower upper
  have second := closed_window_coordinate T rectangles b.val radius (code b) (windows b radius) k lower upper
  rw [← matching k lower upper] at second
  exact diameter_bound_both_closure (rectangles (a.val k)) δ (diameter (a.val k)) _ _ first second

end LeanShared.MarkovFinitePathRealization
