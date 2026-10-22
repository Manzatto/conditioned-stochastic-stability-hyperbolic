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
namespace LeanShared.CompactCenteredAtlasRadius
open Set Filter IsManifold Bundle
open scoped Manifold ContDiff Bundle Topology
open LeanShared.CenteredManifoldCoordinates

set_option maxHeartbeats 1600000 in
theorem exists_radius
    {E M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    (H : M → M) (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (K : Set M) (compact : IsCompact K) (inside : K ⊆ c.source)
    (target : MapsTo H K d.source) (B δ : ℝ) (positiveB : 0 < B) (positiveδ : 0 < δ) :
    ∃ r > 0, ∀ (x : M) (hx : x ∈ K)
      (e : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
      (f : Q ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (H x)),
      ‖e.toContinuousLinearMap‖ ≤ B → ‖f.symm.toContinuousLinearMap‖ ≤ B →
      let L := (e.trans ((CompactRiemannianChartBounds.chart_differentiable c hc).mfderiv
        (inside hx))).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x))
      let R := (f.trans ((CompactRiemannianChartBounds.chart_differentiable d hd).mfderiv
        (target hx))).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (H x)))
      ∀ z : P, ‖z‖ ≤ r →
        c x + L z ∈ c.target ∧ H (c.symm (c x + L z)) ∈ d.source ∧
        DifferentiableAt ℝ (centered L R (c x) (d (H x)) (d ∘ H ∘ c.symm)) z ∧
        ‖fderiv ℝ (centered L R (c x) (d (H x)) (d ∘ H ∘ c.symm)) z -
          f.symm.toContinuousLinearMap.comp
            ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x).comp e.toContinuousLinearMap)‖ < δ := by
  let C := CompactRiemannianChartBounds.chart_differentiable c hc
  let D := CompactRiemannianChartBounds.chart_differentiable d hd
  obtain ⟨Cs, positiveCs, boundCs⟩ := CompactRiemannianChartBounds.forward c hc K compact inside
  obtain ⟨Ct, positiveCt, boundCt⟩ := CompactRiemannianChartBounds.inverse d hd
    (H '' K) (compact.image smooth.continuous) (by rintro _ ⟨x, hx, rfl⟩; exact target hx)
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
  let frameBound := Cs * B + B * Ct + 1
  have positiveFrame : 0 < frameBound := by
    dsimp [frameBound]
    positivity
  obtain ⟨r, positiveR, bound⟩ := BoundedFrameNonlinearRadius.exists_uniform_radius
    (P := P) (Q := Q) (c '' K) compactCenters (d ∘ H ∘ c.symm) rawSmooth
    frameBound δ positiveFrame positiveδ
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
  refine ⟨min r (ρ / frameBound), lt_min positiveR (div_pos positiveρ positiveFrame),
    fun x hx e f he hf => ?_⟩
  dsimp only
  let L := (e.trans (C.mfderiv (inside hx))).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x))
  let R := (f.trans (D.mfderiv (target hx))).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (H x)))
  have source_eq : L.toContinuousLinearMap =
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).toContinuousLinearMap.comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) c x)).comp e.toContinuousLinearMap := by ext v; rfl
  have target_eq : R.symm.toContinuousLinearMap = f.symm.toContinuousLinearMap.comp
      ((D.mfderiv (target hx)).symm.toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (H x))).symm.toContinuousLinearMap) := by ext v; rfl
  have source_bound : ‖L.toContinuousLinearMap‖ ≤ frameBound := by
    rw [source_eq]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (boundCs x hx) he (norm_nonneg _) positiveCs.le)).trans (by
        dsimp [frameBound]; nlinarith [mul_pos positiveB positiveCt])
  have target_bound : ‖R.symm.toContinuousLinearMap‖ ≤ frameBound := by
    rw [target_eq]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hf (boundCt (H x) (mem_image_of_mem H hx)) (norm_nonneg _) positiveB.le)).trans (by
        dsimp [frameBound]; nlinarith [mul_pos positiveCs positiveB])
  intro z hz
  have derivative_small : ‖z‖ ≤ r := hz.trans (min_le_left _ _)
  have displacement : ‖L z‖ ≤ ρ := calc
    ‖L z‖ ≤ ‖L.toContinuousLinearMap‖ * ‖z‖ := L.toContinuousLinearMap.le_opNorm z
    _ ≤ frameBound * ‖z‖ := mul_le_mul_of_nonneg_right source_bound (norm_nonneg z)
    _ ≤ frameBound * (ρ / frameBound) :=
      mul_le_mul_of_nonneg_left (hz.trans (min_le_right _ _)) positiveFrame.le
    _ = ρ := by field_simp
  have valid := inDomain (c x) (mem_image_of_mem c hx) (L z) displacement
  have local_bound := bound (c x) (mem_image_of_mem c hx) L R source_bound target_bound
    (d (H x)) z derivative_small
  have origin := (CenteredAtlasCoordinates.hasFDerivAt_centered H x c d C D
    (inside hx) (target hx) e f (smooth.mdifferentiable one_ne_zero x)).fderiv
  change fderiv ℝ (centered L R (c x) (d (H x)) (d ∘ H ∘ c.symm)) 0 =
    f.symm.toContinuousLinearMap.comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x).comp e.toContinuousLinearMap) at origin
  rw [origin] at local_bound
  exact ⟨valid.1, valid.2, local_bound⟩

end LeanShared.CompactCenteredAtlasRadius
