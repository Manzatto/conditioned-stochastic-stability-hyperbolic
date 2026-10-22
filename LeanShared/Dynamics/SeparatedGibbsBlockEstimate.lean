module

public import LeanShared.Dynamics.SeparatedGibbsEntropy
public import LeanShared.Dynamics.CesaroEntropyBlockEstimate
public import LeanShared.Dynamics.CesaroOrbitEnergy
import Mathlib.Tactic.FieldSimp

/-! The normalized separated Gibbs partition sum is bounded by the
actual Cesaro block free energy, with an explicit vanishing boundary term. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
namespace MeasurablePartition

theorem separated_gibbs_block_estimate (P : MeasurablePartition (X := X) k)
    (T : X → X) (continuous : Continuous T) (φ : X →ᵇ ℝ) (K : Set X) (n : ℕ) (ε : ℝ)
    (s : Finset X) (nonempty : s.Nonempty) (separated : Separated T K (n+1) ε s)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i → dist x y < ε)
    (m : ℕ) (positive : 0 < m) (large : m ≤ n+1) :
    let a : s → ℝ := fun x => orbitSum T φ (n+1) x.val
    let : Nonempty s := nonempty.to_subtype
    let σ := LeanShared.FiniteAtomicProbability.gibbs a Subtype.val
    let bar := LeanShared.CesaroProbability.measure T σ n
    Real.log (∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ) ≤
      dynamicalEntropy P T bar m/m + (∫ x, φ x ∂bar) +
      (2*(m : ℝ)*Real.log (k : ℝ))/(n+1 : ℝ) := by
  let a : s → ℝ := fun x => orbitSum T φ (n+1) x.val
  let : Nonempty s := nonempty.to_subtype
  let σ := LeanShared.FiniteAtomicProbability.gibbs a Subtype.val
  let bar := LeanShared.CesaroProbability.measure T σ n
  have gibbs := P.separated_gibbs_identity T φ K (n+1) ε s nonempty separated mesh
  change dynamicalEntropy P T (σ : Measure X) (n+1) +
    (∫ x, orbitSum T φ (n+1) x ∂(σ : Measure X)) = _ at gibbs
  have energy := LeanShared.CesaroProbability.orbit_energy T continuous σ φ n
  have blocks := P.cesaro_entropy_block_estimate T continuous.measurable σ m n positive large
  change (m : ℝ)*dynamicalEntropy P T (σ : Measure X) (n+1) ≤
    (n+1 : ℝ)*dynamicalEntropy P T bar m + 2*(m : ℝ)*m*Real.log (k : ℝ) at blocks
  have mpos : (0 : ℝ) < m := by exact_mod_cast positive
  have npos : (0 : ℝ) < n+1 := by positivity
  have scaled := div_le_div_of_nonneg_right blocks (mul_nonneg mpos.le npos.le)
  have left : (m : ℝ)*dynamicalEntropy P T (σ : Measure X) (n+1) / ((m : ℝ)*(n+1)) =
      dynamicalEntropy P T (σ : Measure X) (n+1)/(n+1 : ℝ) := by field_simp
  have right : ((n+1 : ℝ)*dynamicalEntropy P T bar m + 2*(m : ℝ)*m*Real.log (k : ℝ)) /
      ((m : ℝ)*(n+1)) = dynamicalEntropy P T bar m/m +
      (2*(m : ℝ)*Real.log (k : ℝ))/(n+1 : ℝ) := by field_simp
  rw [left,right] at scaled
  have identity : dynamicalEntropy P T (σ : Measure X) (n+1)/(n+1 : ℝ) + (∫ x, φ x ∂bar) =
      Real.log (∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ) := by
    rw [←gibbs,energy]
    change _ + _ = (_ + (n+1 : ℝ)*(∫ x, φ x ∂bar))/(n+1 : ℝ)
    field_simp
  change Real.log (∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ) ≤
    dynamicalEntropy P T bar m/m + (∫ x, φ x ∂bar) + _
  linarith

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
