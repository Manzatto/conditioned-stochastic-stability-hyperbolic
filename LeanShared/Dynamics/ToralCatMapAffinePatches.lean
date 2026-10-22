module

public import LeanShared.Dynamics.ToralCatMapTranslations
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! Concrete uniformly sized affine quotient patches. Their compact
closures lie in the selected source chart; their cat-map images and
small translated images lie in the selected target chart. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold Bundle Function Metric
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.ToralCatMap

def patchRadius : ℝ := 1 / 32

def affinePatch (a : ℝ × ℝ) : Set Torus := quotient '' ball a patchRadius

theorem affineChart_source (a : ℝ × ℝ) : (affineChart a).source = (localProjection a).target := by
  simp [affineChart, mfld_simps]

theorem mem_localProjection_source_of_dist_lt (a z : ℝ × ℝ) (small : dist z a < 1 / 2) :
    z ∈ (localProjection a).source := by
  have first : |z.1 - a.1| < 1 / 2 :=
    lt_of_le_of_lt (norm_fst_le (z - a)) (by simpa only [dist_eq_norm] using small)
  have second : |z.2 - a.2| < 1 / 2 :=
    lt_of_le_of_lt (norm_snd_le (z - a)) (by simpa only [dist_eq_norm] using small)
  have f := abs_lt.mp first
  have s := abs_lt.mp second
  change z.1 ∈ Ioo (a.1 - 1 / 2) (a.1 - 1 / 2 + 1) ∧
    z.2 ∈ Ioo (a.2 - 1 / 2) (a.2 - 1 / 2 + 1)
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem closedBall_subset_localProjection (a : ℝ × ℝ) :
    closedBall a patchRadius ⊆ (localProjection a).source := by
  intro z hz
  exact mem_localProjection_source_of_dist_lt a z
    ((mem_closedBall.mp hz).trans_lt (by norm_num [patchRadius]))

theorem affinePatch_open (a : ℝ × ℝ) : IsOpen (affinePatch a) :=
  (localProjection a).isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans (closedBall_subset_localProjection a))

theorem quotient_mem_affinePatch (a : ℝ × ℝ) : quotient a ∈ affinePatch a :=
  mem_image_of_mem quotient (mem_ball_self (by norm_num [patchRadius]))

theorem affinePatch_closure_subset (a : ℝ × ℝ) :
    closure (affinePatch a) ⊆ quotient '' closedBall a patchRadius :=
  closure_minimal (image_mono ball_subset_closedBall)
    ((isCompact_closedBall a patchRadius).image smooth_quotient.continuous).isClosed

theorem affinePatch_compact (a : ℝ × ℝ) : IsCompact (closure (affinePatch a)) :=
  ((isCompact_closedBall a patchRadius).image smooth_quotient.continuous).of_isClosed_subset
    isClosed_closure (affinePatch_closure_subset a)

theorem affinePatch_source (a : ℝ × ℝ) : closure (affinePatch a) ⊆ (affineChart a).source := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := affinePatch_closure_subset a hx
  rw [affineChart_source]
  exact (localProjection a).map_source (closedBall_subset_localProjection a hz)

theorem norm_map_le (z : ℝ × ℝ) : ‖map z‖ ≤ 3 * ‖z‖ := by
  change max ‖z.1 + z.1 + z.2‖ ‖z.1 + z.2‖ ≤ 3 * ‖z‖
  have first := norm_fst_le z
  have second := norm_snd_le z
  apply max_le
  · have bound := norm_add_le (z.1 + z.1) z.2
    have doubled := norm_add_le z.1 z.1
    linarith
  · have bound := norm_add_le z.1 z.2
    linarith [norm_nonneg z]

theorem dist_map_le (z a : ℝ × ℝ) : dist (map z) (map a) ≤ 3 * dist z a := by
  change ‖linear z - linear a‖ ≤ 3 * ‖z - a‖
  rw [← linear.map_sub]
  exact norm_map_le (z - a)

theorem small_perturbed_lift_source (a z : ℝ × ℝ) (u : Control)
    (state : z ∈ closedBall a patchRadius) (control : ‖u‖ ≤ patchRadius) :
    controlEquivalence u + map z ∈ (localProjection (map a)).source := by
  apply mem_localProjection_source_of_dist_lt
  have ctrl : ‖controlEquivalence u‖ ≤ ‖u‖ :=
    max_le (norm_le_pi_norm u 0) (norm_le_pi_norm u 1)
  have addition : dist (controlEquivalence u + map z) (map a) ≤
      ‖controlEquivalence u‖ + dist (map z) (map a) := by
    simpa only [dist_eq_norm, add_sub_assoc] using norm_add_le (controlEquivalence u) (map z - map a)
  have expanded := dist_map_le z a
  have nearby := mem_closedBall.mp state
  have positive : 0 ≤ patchRadius := by norm_num [patchRadius]
  nlinarith [show patchRadius = 1 / 32 from rfl]

theorem perturbation_affinePatch_target (a : ℝ × ℝ) (u : Control) (control : ‖u‖ ≤ patchRadius) :
    perturbation u '' closure (affinePatch a) ⊆ (affineChart (map a)).source := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, rfl⟩ := affinePatch_closure_subset a hx
  rw [affineChart_source]
  have equal : perturbation u (quotient z) = quotient (controlEquivalence u + map z) := by
    ext <;> simp [perturbation, quotient, map, controlEquivalence]
  rw [equal]
  exact (localProjection (map a)).map_source (small_perturbed_lift_source a z u hz control)

def affineCoordinatePatch (a : ℝ × ℝ) : Set HilbertModel :=
  (affineChart a).target ∩ (affineChart a).symm ⁻¹' affinePatch a

theorem affineCoordinatePatch_eq (a : ℝ × ℝ) :
    affineCoordinatePatch a = quotientCoordinateEquivalence '' ball a patchRadius := by
  ext y
  constructor
  · rintro ⟨hy, z, hz, equal⟩
    refine ⟨z, hz, ?_⟩
    have chart := congrArg (affineChart a) equal
    rw [(affineChart a).right_inv hy] at chart
    exact (affineChart_quotient a z
      (closedBall_subset_localProjection a (ball_subset_closedBall hz))).symm.trans chart
  · rintro ⟨z, hz, rfl⟩
    have inside := closedBall_subset_localProjection a (ball_subset_closedBall hz)
    have source : quotient z ∈ (affineChart a).source := by
      rw [affineChart_source]
      exact (localProjection a).map_source inside
    refine ⟨?_, ?_⟩
    · rw [← affineChart_quotient a z inside]
      exact (affineChart a).map_source source
    · change (affineChart a).symm (quotientCoordinateEquivalence z) ∈ affinePatch a
      rw [affineChart_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact mem_image_of_mem quotient hz

theorem affineCoordinatePatch_open (a : ℝ × ℝ) : IsOpen (affineCoordinatePatch a) := by
  rw [affineCoordinatePatch_eq]
  exact quotientCoordinateEquivalence.toHomeomorph.isOpenMap _ isOpen_ball

def affineCoordinate (u : Control) (y : HilbertModel) : HilbertModel :=
  quotientCoordinateEquivalence (controlEquivalence u + map (quotientCoordinateEquivalence.symm y))

theorem perturbation_affine_coordinate (a : ℝ × ℝ) (u : Control) (control : ‖u‖ ≤ patchRadius)
    (y : HilbertModel) (state : y ∈ affineCoordinatePatch a) :
    affineChart (map a) (perturbation u ((affineChart a).symm y)) = affineCoordinate u y := by
  rw [affineChart_symm_apply]
  have lift : quotientCoordinateEquivalence.symm y ∈ ball a patchRadius := by
    rw [affineCoordinatePatch_eq] at state
    obtain ⟨z, hz, rfl⟩ := state
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz
  have equal : perturbation u (quotient (quotientCoordinateEquivalence.symm y)) =
      quotient (controlEquivalence u + map (quotientCoordinateEquivalence.symm y)) := by
    ext <;> simp [perturbation, quotient, controlEquivalence, map]
  rw [equal, affineChart_quotient _ _
    (small_perturbed_lift_source a _ u (ball_subset_closedBall lift) control)]
  rfl

def affineLinear : HilbertModel →L[ℝ] HilbertModel :=
  quotientCoordinateEquivalence.toContinuousLinearMap.comp
    (linear.toContinuousLinearMap.comp quotientCoordinateEquivalence.symm.toContinuousLinearMap)

theorem affineCoordinate_formula (u : Control) (y : HilbertModel) :
    affineCoordinate u y = quotientCoordinateEquivalence (controlEquivalence u) + affineLinear y :=
  quotientCoordinateEquivalence.map_add _ _

theorem smooth_affineCoordinate (u : Control) : ContDiff ℝ ∞ (affineCoordinate u) := by
  have equal : affineCoordinate u = fun y => quotientCoordinateEquivalence (controlEquivalence u) + affineLinear y :=
    funext (affineCoordinate_formula u)
  rw [equal]
  exact contDiff_const.add affineLinear.contDiff

end LeanShared.ToralCatMap
