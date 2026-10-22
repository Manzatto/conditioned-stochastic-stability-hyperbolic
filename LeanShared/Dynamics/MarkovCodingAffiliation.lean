module

public import LeanShared.Dynamics.MarkovCodingMatchingWindow

/-! Equality of the literal refined coding is a finite-type relation:
two words code the same point exactly when their rectangle labels are
affiliated at every time.  Affiliation is actual intersection of closed
rectangles, and the equivalence is derived from diameter and expansivity.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding
open scoped Topology
variable {X I : Type*} [MetricSpace X]

@[expose] def Affiliated (rectangles : I → Set X) (i j : I) : Prop :=
  (closure (rectangles i) ∩ closure (rectangles j)).Nonempty

/-- The two finite symbolic properties needed by the signed fiber construction.
This predicate is an output of the actual hyperbolic coding construction. -/
@[expose] def HasSymbolicFiberGeometry (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X) : Prop :=
  (∀ a b, code a = code b ↔ ∀ k : ℤ, Affiliated rectangles (a.val k) (b.val k)) ∧
  ∀ a b, code a = code b → ∀ radius : ℕ,
    a.val (-(radius : ℤ)) = b.val (-(radius : ℤ)) → a.val radius = b.val radius →
    ∀ k : ℤ, -(radius : ℤ) ≤ k → k ≤ radius → a.val k = b.val k

theorem coding_eq_iff_affiliated (T : X ≃ₜ X) (rectangles : I → Set X) (δ c : ℝ)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c)
    (diameter : ∀ i, ∀ x ∈ rectangles i, ∀ y ∈ rectangles i, dist x y ≤ δ)
    (code : Path (Transition T rectangles) → X)
    (windows : ∀ a radius, code a ∈ closure (itineraryWindow T rectangles a.val radius))
    (a b : Path (Transition T rectangles)) :
    code a = code b ↔ ∀ k : ℤ, Affiliated rectangles (a.val k) (b.val k) := by
  have orbitInside (p : Path (Transition T rectangles)) (k : ℤ) :
      (T ^ k) (code p) ∈ closure (rectangles (p.val k)) :=
    closed_window_coordinate T rectangles p.val k.natAbs (code p) (windows p k.natAbs) k (by omega) (by omega)
  constructor
  · intro equal k
    exact ⟨(T ^ k) (code a), orbitInside a k, equal.symm ▸ orbitInside b k⟩
  · intro affiliated
    have close (k : ℤ) : dist ((T ^ k) (code a)) ((T ^ k) (code b)) ≤ c := by
      obtain ⟨q, insideA, insideB⟩ := affiliated k
      have first := diameter_bound_both_closure (rectangles (a.val k)) δ (diameter (a.val k))
        _ q (orbitInside a k) insideA
      have second := diameter_bound_both_closure (rectangles (b.val k)) δ (diameter (b.val k))
        _ q (orbitInside b k) insideB
      have triangle := dist_triangle ((T ^ k) (code a)) q ((T ^ k) (code b))
      rw [dist_comm q] at triangle
      linarith
    apply expansive
    intro n
    constructor
    · simpa only [zpow_natCast, DiffeomorphismIterates.coe_pow] using close n
    · have estimate := close (-(n : ℤ))
      rw [zpow_neg, zpow_natCast] at estimate
      change dist ((T ^ n).symm (code a)) ((T ^ n).symm (code b)) ≤ c at estimate
      simpa only [DiffeomorphismIterates.coe_symm_pow] using estimate

end LeanShared.MarkovFinitePathRealization
