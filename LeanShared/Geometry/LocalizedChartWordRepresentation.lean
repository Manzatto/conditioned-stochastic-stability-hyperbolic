module
public import LeanShared.Geometry.ChartedHomeomorphCoordinateMap
public import LeanShared.Geometry.SupportedChartExtension
import Mathlib.Tactic.Ring

/-! Agreement on a neighborhood of the literal amplitude support gives
the global physical weighted-composition formula. Away from that support
the amplitude is zero, so no global chart or orbit agreement is required. -/
public noncomputable section
open Set
namespace LeanShared.LocalizedChartWordRepresentation
variable {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M]

theorem represented (c d : OpenPartialHomeomorph M E) (native : M ≃ₜ M)
    (G : E → E) (θ a : M → ℂ) (f : E → ℂ) {O : Set E}
    (support : tsupport (ChartLocalization.coordinate c θ a) ⊆ O)
    (inside : O ⊆ (ChartedHomeomorphCoordinateMap.coordinateMap c d native).source)
    (agree : EqOn G (ChartedHomeomorphCoordinateMap.coordinateMap c d native) O) (y : E) :
    ChartLocalization.coordinate c θ
      (fun m => a m * SupportedChartExtension.function d f (native m)) y =
      ChartLocalization.coordinate c θ a y * f (G y) := by
  classical
  by_cases target : y ∈ c.target
  · simp only [ChartLocalization.coordinate, ite_eq_left target]
    by_cases zero : θ (c.symm y) * a (c.symm y) = 0
    · rw [← mul_assoc, zero, zero_mul, zero_mul]
    · have member : y ∈ tsupport (ChartLocalization.coordinate c θ a) :=
        subset_tsupport _ (by
          change ChartLocalization.coordinate c θ a y ≠ 0
          simpa only [ChartLocalization.coordinate, ite_eq_left target] using zero)
      have inO := support member
      have source := (ChartedHomeomorphCoordinateMap.coordinateMap_source c d native y).mp (inside inO)
      have value := agree inO
      simp only [SupportedChartExtension.function, ite_eq_left source.2]
      rw [value, ChartedHomeomorphCoordinateMap.coordinateMap_apply]
      exact (mul_assoc _ _ _).symm
  · simp only [ChartLocalization.coordinate, ite_eq_right target, zero_mul]

end LeanShared.LocalizedChartWordRepresentation
