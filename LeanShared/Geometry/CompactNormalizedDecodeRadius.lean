module
public import LeanShared.Geometry.CompactNormalizedChartTube

/-! Arbitrarily small normalized coordinates give an actual uniform
ambient distance from the compact reference patch, for EVERY bounded
normalization. The original ambient metric is retained. -/
public noncomputable section
open Set Metric
namespace LeanShared.CompactNormalizedDecodeRadius
variable {M E P : Type*} [MetricSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem exists_radius (c : OpenPartialHomeomorph M E) (K : Set M)
    (compact : IsCompact K) (inside : K ⊆ c.source) (B : ℝ) (nonnegativeB : 0 ≤ B)
    (η : ℝ) (positiveη : 0 < η) :
    ∃ radius > 0, ∀ x ∈ K, ∀ L : P →L[ℝ] E, ‖L‖ ≤ B → ∀ z, ‖z‖ ≤ radius →
      c x+L z ∈ c.target ∧ dist (c.symm (c x+L z)) x < η := by
  obtain ⟨R₀,positiveR₀,S,compactS,insideS,tube⟩ :=
    CompactNormalizedChartTube.exists_tube (P := P) c K compact inside B nonnegativeB
  have subsetS : K ⊆ S := by
    intro x hx
    have facts := tube x hx (0 : P →L[ℝ] E) (by simpa only [norm_zero] using nonnegativeB) 0
      (by simpa only [norm_zero] using positiveR₀.le)
    simpa only [zero_apply,add_zero,c.left_inv (inside hx)] using facts.2
  have compactCoordinates : IsCompact (c '' S) :=
    compactS.image_of_continuousOn (c.continuousOn.mono insideS)
  have validCoordinates : c '' S ⊆ c.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact c.map_source (insideS hx)
  have uniform := compactCoordinates.uniformContinuousOn_of_continuous
    (c.symm.continuousOn.mono validCoordinates)
  obtain ⟨δ,positiveδ,control⟩ := Metric.uniformContinuousOn_iff.mp uniform η positiveη
  let r := δ/(B+1)
  have positiveR : 0 < r := div_pos positiveδ (by linarith)
  have normalization : (B+1)*r = δ := by dsimp only [r]; field_simp
  refine ⟨min R₀ r,lt_min positiveR₀ positiveR,?_⟩
  intro x hx L bound z small
  have actual := tube x hx L bound z (small.trans (min_le_left _ _))
  have closeCoordinates : dist (c x+L z) (c x) < δ := by
    rw [dist_eq_norm,add_sub_cancel_left]
    have estimate := (L.le_opNorm z).trans
      (mul_le_mul bound (small.trans (min_le_right R₀ r)) (norm_nonneg z) nonnegativeB)
    nlinarith
  have sourceMember : c x ∈ c '' S := mem_image_of_mem c (subsetS hx)
  have targetMember : c x+L z ∈ c '' S := by
    refine ⟨c.symm (c x+L z),actual.2,?_⟩
    exact c.right_inv actual.1
  refine ⟨actual.1,?_⟩
  have decoded := control (c x+L z) targetMember (c x) sourceMember closeCoordinates
  simpa only [c.left_inv (inside hx)] using decoded

end LeanShared.CompactNormalizedDecodeRadius
