module

public import LeanShared.Analysis.ParameterizedContraction
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Genuine finite two-boundary Lyapunov--Perron transformation. The initial
stable coordinate and final unstable coordinate are prescribed independently.
The contraction constant is uniform in the segment length, including zero. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform
open scoped NNReal

structure Data (U S : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] (N : ℕ) where
  expanding : Fin N → U ≃L[ℝ] U
  contracting : Fin N → S →L[ℝ] S
  nonlinear : Fin N → U × S → U × S
  k : ℝ≥0
  δ : ℝ≥0
  small : k + δ < 1
  inverse_bound : ∀ i, LipschitzWith k (expanding i).symm
  stable_bound : ∀ i, LipschitzWith k (contracting i)
  nonlinear_bound : ∀ i, LipschitzWith δ (nonlinear i)
  nonlinear_zero : ∀ i, nonlinear i 0 = 0

namespace Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] {N : ℕ}

theorem k_le_one (d : Data U S N) : d.k ≤ 1 :=
  (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ d.δ from zero_le)).trans d.small.le

@[expose] def raw (d : Data U S N) (boundary : U × S)
    (z : Fin (N + 1) → U × S) (j : Fin (N + 1)) : U × S :=
  ((if h : j.val < N then (d.expanding ⟨j.val, h⟩).symm
      ((z ⟨j.val + 1, by omega⟩).1 - (d.nonlinear ⟨j.val, h⟩ (z j)).1) else boundary.1),
    if h : 0 < j.val then d.contracting ⟨j.val - 1, by omega⟩ (z ⟨j.val - 1, by omega⟩).2 +
      (d.nonlinear ⟨j.val - 1, by omega⟩ (z ⟨j.val - 1, by omega⟩)).2 else boundary.2)

set_option maxHeartbeats 1000000 in
theorem raw_distance (d : Data U S N) (boundary : U × S)
    (z w : Fin (N + 1) → U × S) (D : ℝ)
    (distance : ∀ j, dist (z j) (w j) ≤ D) (j : Fin (N + 1)) :
    dist (d.raw boundary z j) (d.raw boundary w j) ≤ (d.k + d.δ : ℝ≥0) * D := by
  have nonnegativeD : 0 ≤ D := (dist_nonneg (x := z ⟨0, by omega⟩) (y := w ⟨0, by omega⟩)).trans (distance _)
  have fst (m : Fin (N + 1)) : dist (z m).1 (w m).1 ≤ D := (le_max_left _ _).trans (distance m)
  have snd (m : Fin (N + 1)) : dist (z m).2 (w m).2 ≤ D := (le_max_right _ _).trans (distance m)
  have nonlinear (i : Fin N) (m : Fin (N + 1)) :
      dist (d.nonlinear i (z m)) (d.nonlinear i (w m)) ≤ d.δ * D :=
    ((d.nonlinear_bound i).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (distance m) d.δ.coe_nonneg)
  have unstable (i : Fin N) (m l : Fin (N + 1)) :
      dist ((d.expanding i).symm ((z l).1 - (d.nonlinear i (z m)).1))
        ((d.expanding i).symm ((w l).1 - (d.nonlinear i (w m)).1)) ≤ (d.k + d.δ : ℝ≥0) * D := by
    have perturbation := (le_max_left _ _).trans (nonlinear i m)
    calc
      _ ≤ d.k * dist ((z l).1 - (d.nonlinear i (z m)).1)
          ((w l).1 - (d.nonlinear i (w m)).1) := (d.inverse_bound i).dist_le_mul _ _
      _ ≤ d.k * (dist (z l).1 (w l).1 + dist (d.nonlinear i (z m)).1 (d.nonlinear i (w m)).1) :=
        mul_le_mul_of_nonneg_left (dist_sub_sub_le _ _ _ _) d.k.coe_nonneg
      _ ≤ (d.k : ℝ) * (D + d.δ * D) :=
        mul_le_mul_of_nonneg_left (add_le_add (fst l) perturbation) d.k.coe_nonneg
      _ ≤ _ := by
        have hk : (d.k : ℝ) ≤ 1 := d.k_le_one
        rw [NNReal.coe_add]
        nlinarith [mul_nonneg d.δ.coe_nonneg nonnegativeD]
  have stable (i : Fin N) (m : Fin (N + 1)) :
      dist (d.contracting i (z m).2 + (d.nonlinear i (z m)).2)
        (d.contracting i (w m).2 + (d.nonlinear i (w m)).2) ≤ (d.k + d.δ : ℝ≥0) * D := by
    calc
      _ ≤ dist (d.contracting i (z m).2) (d.contracting i (w m).2) +
          dist (d.nonlinear i (z m)).2 (d.nonlinear i (w m)).2 := dist_add_add_le _ _ _ _
      _ ≤ (d.k : ℝ) * D + d.δ * D := add_le_add
        (((d.stable_bound i).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (snd m) d.k.coe_nonneg))
        ((le_max_right _ _).trans (nonlinear i m))
      _ = _ := by rw [NNReal.coe_add, add_mul]
  change max (dist _ _) (dist _ _) ≤ _
  apply max_le
  · by_cases before : j.val < N
    · simpa only [raw, dite_eq_left before] using unstable ⟨j.val, before⟩ j ⟨j.val + 1, by omega⟩
    · simp only [raw, dite_eq_right before, dist_self]
      exact mul_nonneg (d.k + d.δ).coe_nonneg nonnegativeD
  · by_cases after : 0 < j.val
    · simpa only [raw, dite_eq_left after] using stable ⟨j.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
    · simp only [raw, dite_eq_right after, dist_self]
      exact mul_nonneg (d.k + d.δ).coe_nonneg nonnegativeD

theorem transform_contracting (d : Data U S N) (boundary : U × S) :
    ContractingWith (d.k + d.δ) (d.raw boundary) := by
  refine ⟨d.small, LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  apply (dist_pi_le_iff (mul_nonneg (d.k + d.δ).coe_nonneg dist_nonneg)).mpr
  intro j
  exact d.raw_distance boundary z w (dist z w) (dist_le_pi_dist z w) j

end Data
end LeanShared.FiniteBoundaryHyperbolicTransform
