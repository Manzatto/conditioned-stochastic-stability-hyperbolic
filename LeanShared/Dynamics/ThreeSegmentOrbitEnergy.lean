module
public import LeanShared.Dynamics.OrbitEnergyConcatenation

/-! Three prescribed orbit pieces lose only two transition lengths and
three uniform Bowen distortions. All seam times are literal iterate times. -/
public section
open Set
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*}

theorem orbitSum_three_gluing_lower (T : X → X) (φ : X → ℝ) (K : Set X)
    (invariant : MapsTo T K K) (B : ℝ) (lower : ∀ x ∈ K, -B ≤ φ x)
    (n k m gap : ℕ) (positiveGap : 0 < gap) (x z y w : X) (hw : w ∈ K)
    (D : ℝ)
    (first : |orbitSum T φ (n + 1) w - orbitSum T φ (n + 1) x| ≤ D)
    (middle : |orbitSum T φ (k + 1) (T^[n + gap] w) - orbitSum T φ (k + 1) z| ≤ D)
    (last : |orbitSum T φ (m + 1) (T^[n + gap + k + gap] w) - orbitSum T φ (m + 1) y| ≤ D) :
    orbitSum T φ (n + 1) x + orbitSum T φ (k + 1) z + orbitSum T φ (m + 1) y -
      3 * D - 2 * (gap - 1 : ℕ) * B ≤ orbitSum T φ (n + gap + k + gap + m + 1) w := by
  have tail := orbitSum_gluing_lower T φ K invariant B lower k m gap positiveGap z y
    (T^[n + gap] w) (invariant.iterate (n + gap) hw) D middle (by
      have time : T^[k + gap] (T^[n + gap] w) = T^[n + gap + k + gap] w := by
        rw [← Function.iterate_add_apply]
        congr 1
        omega
      rw [time]
      exact last)
  have size : n + gap + k + gap + m + 1 = (n + 1) + ((gap - 1) + (k + gap + m + 1)) := by omega
  rw [size, orbitSum_add T φ (n + 1) ((gap - 1) + (k + gap + m + 1)) w,
    orbitSum_add T φ (gap - 1) (k + gap + m + 1) (T^[n + 1] w)]
  have time : T^[gap - 1] (T^[n + 1] w) = T^[n + gap] w := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [time]
  have transition := orbitSum_lower T φ K invariant B lower (gap - 1)
    (invariant.iterate (n + 1) hw)
  have initial := (abs_le.mp first).1
  linarith

end LeanShared.ThermodynamicDefinitions
