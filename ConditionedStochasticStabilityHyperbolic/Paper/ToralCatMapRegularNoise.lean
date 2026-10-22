module

public import ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMapNoiseAtlas
public import LeanShared.Dynamics.ToralCatMapAffineJets

/-! Literal regular-noise maps for the concrete cat map, at every r>1.
The finite atlas and all Whitney bounds are constructed. Affine quotient
coordinates make every positive-order perturbation-jet difference zero. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold Bundle Function Filter
open scoped Manifold ContDiff Bundle Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMap
open LeanShared LeanShared.ToralCatMap

theorem noiseAtlas_coordinate_jet (u : Control) (small : ‖u‖ ≤ patchRadius)
    (i : Fin noiseAtlas.count) (k : ℕ) (y : Model) (hy : y ∈ noiseAtlas.coordinatePatch i) :
    iteratedFDeriv ℝ k (noiseAtlas.coordinate (perturbation u) i) y =
      iteratedFDeriv ℝ k (affineCoordinate u) y := by
  have nearby : noiseAtlas.coordinate (perturbation u) i =ᶠ[𝓝 y] affineCoordinate u := by
    apply eventually_of_mem ((affineCoordinatePatch_open (patchCenter i)).mem_nhds hy)
    intro z hz
    exact noiseAtlas_coordinate u small i z hz
  exact (nearby.iteratedFDeriv ℝ k).eq_of_nhds

theorem noiseAtlas_reference_jet (i : Fin noiseAtlas.count) (k : ℕ) (y : Model)
    (hy : y ∈ noiseAtlas.coordinatePatch i) :
    iteratedFDeriv ℝ k (noiseAtlas.coordinate LeanShared.ToralCatMap.homeomorph i) y =
      iteratedFDeriv ℝ k (affineCoordinate 0) y := by
  have nearby : noiseAtlas.coordinate LeanShared.ToralCatMap.homeomorph i =ᶠ[𝓝 y] affineCoordinate 0 := by
    apply eventually_of_mem ((affineCoordinatePatch_open (patchCenter i)).mem_nhds hy)
    intro z hz
    exact noiseAtlas_reference_coordinate i z hz
  exact (nearby.iteratedFDeriv ℝ k).eq_of_nhds

theorem noise_whitney_bound (r : ℝ) (hr : 1 < r) (u : Control) (small : ‖u‖ ≤ patchRadius) :
    noiseAtlas.Bound r (perturbation u) (noiseConstant * ‖u‖) where
  uniform x := (perturbation_uniform u x).trans (by
    have one : 1 ≤ noiseConstant := by dsimp [noiseConstant]; linarith [norm_nonneg quotientCoordinateEquivalence.toContinuousLinearMap]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right one (norm_nonneg u))
  target_control i := perturbation_affinePatch_target (patchCenter i) u small
  derivatives i k _ y hy := by
    rw [noiseAtlas_coordinate_jet u small i k y hy, noiseAtlas_reference_jet i k y hy]
    exact affineCoordinate_jet_difference_bound u k y
  holder _ i y hy z hz := by
    have positive : 0 < ⌊r⌋₊ := Nat.floor_pos.mpr hr.le
    rw [noiseAtlas_coordinate_jet u small i _ y hy, noiseAtlas_reference_jet i _ y hy,
      noiseAtlas_coordinate_jet u small i _ z hz, noiseAtlas_reference_jet i _ z hz,
      affineCoordinate_jet_difference_zero u _ positive.ne',
      affineCoordinate_jet_difference_zero u _ positive.ne', sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg noiseConstant_positive.le (norm_nonneg u))
      (Real.rpow_nonneg (norm_nonneg (y - z)) _)

def noiseWindow : ℝ≥0 := ⟨patchRadius, by norm_num [patchRadius]⟩

theorem control_small {ε : ℝ≥0} (window : ε ≤ noiseWindow)
    (u : RegularNoise.cube (ι := Fin 2) ε) : ‖u.val‖ ≤ patchRadius := by
  have bound := NoiseCubeRescaling.cube_norm_le (ε : ℝ) ε.property u
  exact bound.trans (show (ε : ℝ) ≤ patchRadius from window)

def noise (r : ℝ) (hr : 1 < r) : RegularNoise.Maps (E := Model) (ι := Fin 2)
    LeanShared.ToralCatMap.homeomorph r where
  window := noiseWindow
  window_positive := by
    change (0 : ℝ) < patchRadius
    norm_num [patchRadius]
  family _ := perturbation
  atlas := noiseAtlas
  constant := noiseConstant
  constant_positive := noiseConstant_positive
  map_regular _ _ _ control := FractionalManifoldRegularity.regular_map_of_smooth
    (smooth_perturbation_fixed control.val) (zero_lt_one.trans hr).le
  joint_C1 _ _ _ := ⟨univ, isOpen_univ, subset_univ _,
    (smooth_perturbation.of_le (by simp)).contMDiffOn⟩
  control_surjective _ _ _ control x := perturbation_control_surjective control.val x
  whitney_bound _ _ window control := noise_whitney_bound r hr control.val (control_small window control)

end ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMap
