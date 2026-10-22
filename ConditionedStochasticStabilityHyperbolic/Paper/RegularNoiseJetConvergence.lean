module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCenteredDifferential
public import LeanShared.Analysis.FiniteJetComposition
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Literal Whitney estimates imply moving-point C¹ jet convergence in every
actual finite atlas patch. This is independent of laws and of continuity in
noise scale, and supplies the input for finite noisy compositions. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal

 theorem WhitneyAtlas.Bound.coordinate_values_close
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] {T : M → M}
    {A : WhitneyAtlas (E := E) T} {r : ℝ} {f : M → M} {δ : ℝ}
    (b : A.Bound r f δ) (i : Fin A.count) (y : E) (inside : y ∈ A.coordinatePatch i) :
    ‖A.coordinate f i y - A.coordinate T i y‖ ≤ δ := by
  have bound := b.derivatives i 0 (Nat.zero_le _) y inside
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map] using bound

 theorem Maps.coordinate_jetConvergesOn
    {E M ι A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (ε : A → ℝ≥0) (controls : ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (i : Fin F.atlas.count) :
    LeanShared.FiniteJetComposition.JetConvergesOn
      (fun a => F.atlas.coordinate (F.family (ε a) (controls a).val) i)
      (F.atlas.coordinate T i) l (F.atlas.coordinatePatch i) := by
  have smooth : ∀ y ∈ F.atlas.coordinatePatch i,
      ContDiffAt ℝ 1 (F.atlas.coordinate T i) y := by
    intro y hy
    have source : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (F.atlas.source i).symm y :=
      (contMDiffAt_symm_of_mem_maximalAtlas (F.atlas.source_smooth i) hy.1).of_le (by simp)
    have middle := deterministic.contMDiffAt.comp y source
    have target : T ((F.atlas.source i).symm y) ∈ (F.atlas.target i).source :=
      F.atlas.deterministic_target i (mem_image_of_mem T (subset_closure hy.2))
    have last : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (F.atlas.target i)
        (T ((F.atlas.source i).symm y)) :=
      (contMDiffAt_of_mem_maximalAtlas (F.atlas.target_smooth i) target).of_le (by simp)
    exact (last.comp y middle).contDiffAt
  apply LeanShared.FiniteJetComposition.of_local_bounds _ _ l _ smooth
  intro y hy v hv
  have openPatch : IsOpen (F.atlas.coordinatePatch i) :=
    (F.atlas.source i).isOpen_inter_preimage_symm (F.atlas.patch_open i)
  have inside : ∀ᶠ a in l, v a ∈ F.atlas.coordinatePatch i :=
    hv.eventually (openPatch.mem_nhds hy)
  have window : ∀ᶠ a in l, ε a ≤ F.window :=
    (limit.eventually (gt_mem_nhds F.window_positive)).mono (fun _ h => h.le)
  have real_limit : Tendsto (fun a => (ε a : ℝ)) l (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.continuousAt.tendsto.comp limit)
  refine ⟨fun a => F.constant * (ε a : ℝ), ?_, ?_, ?_, ?_⟩
  · simpa only [mul_zero] using real_limit.const_mul F.constant
  · filter_upwards [positive, window, inside] with a ha hw hi
    exact ((F.whitney_bound (ε a) ha hw (controls a)).coordinate_values_close i (v a) hi).trans
      (mul_le_mul_of_nonneg_left (LeanShared.NoiseCubeRescaling.cube_norm_le
        (ε a : ℝ) (ε a).property (controls a)) F.constant_positive.le)
  · filter_upwards [positive, window, inside] with a ha hw hi
    exact F.coordinate_fderiv_close regularity (ε a) ha hw (controls a) i (v a) hi
  · filter_upwards [positive, window, inside] with a ha hw hi
    exact F.atlas.coordinate_differentiableAt
      ((F.map_regular (ε a) ha hw (controls a)).mdifferentiable regularity)
      (F.whitney_bound (ε a) ha hw (controls a)).target_control i (v a) hi

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
