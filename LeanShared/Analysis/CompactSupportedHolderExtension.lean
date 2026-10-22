module
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A quantitative Holder estimate near one fixed compact support extends
globally, uniformly over an arbitrary parameter set. -/
public noncomputable section
open Set
namespace LeanShared.CompactSupportedHolderExtension
variable {E F P : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem exists_bound {S K : Set E} (compact : IsCompact S)
    (inside : S ⊆ interior K) {a B H : ℝ} (ha : 0 ≤ a)
    (hB : 0 ≤ B) (hH : 0 ≤ H) (f : P → E → F)
    (zero : ∀p x, x ∉ S → f p x = 0)
    (value : ∀p x, ‖f p x‖ ≤ B)
    (local_bound : ∀p x, x ∈ K → ∀y, y ∈ K →
      ‖f p x - f p y‖ ≤ H * ‖x-y‖^a) :
    ∃C : ℝ, 0 ≤ C ∧ ∀p x y, ‖f p x-f p y‖ ≤ C*‖x-y‖^a := by
  obtain ⟨δ, hδ, collar⟩ := compact.exists_thickening_subset_open isOpen_interior inside
  let C := H + 2*B / δ^a
  have hpow : 0 < δ^a := Real.rpow_pos_of_pos hδ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have Hle : H ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C, hC, ?_⟩
  intro p x y
  by_cases small : ‖x-y‖ < δ
  · by_cases hx : x ∈ S
    · have hy : y ∈ K := interior_subset (collar
        (Metric.mem_thickening_iff.mpr ⟨x,hx,by simpa [dist_eq_norm,norm_sub_rev] using small⟩))
      exact (local_bound p x (interior_subset (inside hx)) y hy).trans
        (mul_le_mul_of_nonneg_right Hle (Real.rpow_nonneg (norm_nonneg _) _))
    · by_cases hy : y ∈ S
      · have hxK : x ∈ K := interior_subset (collar
          (Metric.mem_thickening_iff.mpr ⟨y,hy,by simpa [dist_eq_norm] using small⟩))
        exact (local_bound p x hxK y (interior_subset (inside hy))).trans
          (mul_le_mul_of_nonneg_right Hle (Real.rpow_nonneg (norm_nonneg _) _))
      · rw [zero p x hx,zero p y hy,sub_self,norm_zero]
        positivity
  · have power : δ^a ≤ ‖x-y‖^a :=
      Real.rpow_le_rpow hδ.le (le_of_not_gt small) ha
    have far : 2*B ≤ (2*B/δ^a)*‖x-y‖^a := by
      calc
        _ = (2*B/δ^a)*δ^a := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left power (by positivity)
    exact (norm_sub_le _ _).trans ((add_le_add (value p x) (value p y)).trans
      ((by linarith : B+B ≤ 2*B).trans (far.trans
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
          (Real.rpow_nonneg (norm_nonneg _) _)))))
end LeanShared.CompactSupportedHolderExtension
