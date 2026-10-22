module
public import LeanShared.Geometry.CenteredAtlasCoordinates
public import LeanShared.Geometry.CompactRiemannianChartBounds
public import LeanShared.Analysis.BoundedFrameNonlinearRadius
public import Mathlib.Tactic.Linarith

/-! Actual fixed-chart nonlinear coordinates on a compact Riemannian set have
one common small derivative radius. All chart and inverse-chart norm bounds
are derived from the continuous metric and actual smooth chart maps. Frames
may be arbitrary pointwise choices with the stated ordinary norm bound. -/
public noncomputable section
namespace LeanShared.CompactMisalignedAtlasRadius
open Set Filter IsManifold Bundle
open scoped Manifold ContDiff Bundle Topology
open LeanShared.CenteredManifoldCoordinates

set_option maxHeartbeats 1600000 in
theorem exists_radius
    {E M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    (H : M → M) (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (K : Set M) (compact : IsCompact K) (inside : K ⊆ c.source)
    (target : MapsTo H K d.source) (C δ : ℝ) (positiveC : 0 < C) (positiveδ : 0 < δ) :
    ∃ r > 0, ∀ (x : M), x ∈ K → ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E),
      ‖L.toContinuousLinearMap‖ ≤ C → ‖R.symm.toContinuousLinearMap‖ ≤ C →
      ∀ b : E, ∀ z : P, ‖z‖ ≤ r →
        c x + L z ∈ c.target ∧ H (c.symm (c x + L z)) ∈ d.source ∧
        DifferentiableAt ℝ (centered L R (c x) b (d ∘ H ∘ c.symm)) z ∧
        ‖fderiv ℝ (centered L R (c x) b (d ∘ H ∘ c.symm)) z -
          fderiv ℝ (centered L R (c x) b (d ∘ H ∘ c.symm)) 0‖ < δ := by
  have compactCenters : IsCompact (c '' K) := compact.image_of_continuousOn
    (c.continuousOn.mono inside)
  have rawSmooth : ∀ a ∈ c '' K, ContDiffAt ℝ 1 (d ∘ H ∘ c.symm) a := by
    rintro _ ⟨x, hx, rfl⟩
    have source : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 c.symm (c x) :=
      (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source (inside hx))).of_le (by simp)
    have middle_at : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H (c.symm (c x)) := by
      rw [c.left_inv (inside hx)]
      exact smooth.contMDiffAt
    have last_at : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 d (H (c.symm (c x))) := by
      rw [c.left_inv (inside hx)]
      exact (contMDiffAt_of_mem_maximalAtlas hd (target hx)).of_le (by simp)
    exact (last_at.comp (c x) (middle_at.comp (c x) source)).contDiffAt
  obtain ⟨r,positiveR,bound⟩ := BoundedFrameNonlinearRadius.exists_uniform_radius
    (P := P) (Q := Q) (c '' K) compactCenters (d ∘ H ∘ c.symm) rawSmooth
    C δ positiveC positiveδ
  let domain : Set E := c.target ∩ c.symm ⁻¹' (H ⁻¹' d.source)
  have openDomain : IsOpen domain :=
    c.isOpen_inter_preimage_symm (d.open_source.preimage smooth.continuous)
  have centerDomain : ∀ a ∈ c '' K, a ∈ domain := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨c.map_source (inside hx), ?_⟩
    change H (c.symm (c x)) ∈ d.source
    rw [c.left_inv (inside hx)]
    exact target hx
  obtain ⟨ρ, positiveρ, inDomain⟩ :=
    CompactCenteredDerivativeBound.exists_radius_of_eventually (c '' K) compactCenters
      (fun z : E × E => z.1 + z.2 ∈ domain) (by
        intro a ha
        have addition : ContinuousAt (fun z : E × E => z.1 + z.2) (a, 0) :=
          continuousAt_fst.add continuousAt_snd
        have nearDomain : ∀ᶠ y in 𝓝 a, y ∈ domain := by
          filter_upwards [openDomain.mem_nhds (centerDomain a ha)] with y hy
          exact hy
        exact addition.tendsto.eventually (by simpa only [add_zero] using nearDomain))
  refine ⟨min r (ρ / C),lt_min positiveR (div_pos positiveρ positiveC),
    fun x hx L R sourceBound targetBound b z hz => ?_⟩
  have displacement : ‖L z‖ ≤ ρ := calc
    ‖L z‖ ≤ ‖L.toContinuousLinearMap‖ * ‖z‖ := L.toContinuousLinearMap.le_opNorm z
    _ ≤ C * ‖z‖ := mul_le_mul_of_nonneg_right sourceBound (norm_nonneg z)
    _ ≤ C * (ρ / C) := mul_le_mul_of_nonneg_left (hz.trans (min_le_right _ _)) positiveC.le
    _ = ρ := by field_simp
  have valid := inDomain (c x) (mem_image_of_mem c hx) (L z) displacement
  exact ⟨valid.1,valid.2,bound (c x) (mem_image_of_mem c hx) L R sourceBound targetBound
    b z (hz.trans (min_le_left _ _))⟩

end LeanShared.CompactMisalignedAtlasRadius
