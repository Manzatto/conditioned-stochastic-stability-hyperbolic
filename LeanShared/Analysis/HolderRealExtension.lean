module

public import Mathlib.Topology.MetricSpace.Snowflaking
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! A genuine scalar Hölder function on an arbitrary subset admits a
same-constant extension. The proof applies the proved real Lipschitz
extension theorem to the actual snowflaked metric. -/
public noncomputable section
namespace LeanShared.HolderRealExtension
open Set Metric
open scoped NNReal
variable {X : Type*} [MetricSpace X]

theorem exists_extension (α C : ℝ) (positive : 0 < α) (small : α ≤ 1) (nonnegative : 0 ≤ C)
    (S : Set X) (f : X → ℝ)
    (bound : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ C * dist x y ^ α) :
    ∃ g : X → ℝ, EqOn f g S ∧ ∀ x y, |g x - g y| ≤ C * dist x y ^ α := by
  let H := Snowflaking X α positive small
  let e : H ≃ₜ X := Snowflaking.homeomorph
  have lip : LipschitzOnWith (⟨C, nonnegative⟩ : ℝ≥0) (fun x : H => f (e x)) (e ⁻¹' S) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change dist (f (e x)) (f (e y)) ≤ C * dist (e x) (e y) ^ α
    rw [Real.dist_eq]
    exact bound (e x) hx (e y) hy
  obtain ⟨g, lipschitz, agreement⟩ := lip.extend_real
  refine ⟨fun x => g (e.symm x), fun x hx => agreement (show e.symm x ∈ e ⁻¹' S by simpa using hx), ?_⟩
  intro x y
  have estimate := lipschitz.dist_le_mul (e.symm x) (e.symm y)
  change dist (g (e.symm x)) (g (e.symm y)) ≤ C * dist x y ^ α at estimate
  simpa only [Real.dist_eq] using estimate

end LeanShared.HolderRealExtension
