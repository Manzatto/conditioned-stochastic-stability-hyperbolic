module

public import ConditionedStochasticStabilityHyperbolic.Paper.InverseUniformControl
public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveCollar
public import LeanShared.Dynamics.ReversibleTransitivity

/-! Ordinary inverse calculus and classical random plaques construct the
actual inverse plaque packet. Zero noise and local covering are derived. -/

@[expose] public noncomputable section
open Set Function Filter Metric IsManifold
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared ControlledPlaqueClosure ReversibleTransitivity
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ}

structure InverseCubeGeometry (F : Maps (E := E) (ι := ι) T r) (ε : ℝ≥0) (V G : Set M) where
  map : Control (ι := ι) × M → M
  joint : ∃ O : Set (Control (ι := ι)), IsOpen O ∧
    (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
    ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1 map (O ×ˢ univ)
  identity : ∀ (a : cube (ι := ι) ε) (y : M),
    ∀ᶠ z in 𝓝 a.val, F.family ε z (map (z, y)) = y
  spatial : ∀ (a : cube (ι := ι) ε) (y : M),
    Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (F.family ε a.val) (map (a.val, y)))
  plaque : (ℤ → cube (ι := ι) ε) → Set M
  lower_semicontinuous : ∀ path : ℤ → cube (ι := ι) ε,
    ∀ paths : ℕ → ℤ → cube (ι := ι) ε, Tendsto paths atTop (𝓝 path) →
      ∀ z ∈ plaque path, ∃ zn : ℕ → M, Tendsto zn atTop (𝓝 z) ∧ ∀ k, zn k ∈ plaque (paths k)
  backward_orbit : ∀ path : ℤ → cube (ι := ι) ε, ∀ z ∈ plaque path,
    ∃ b : ℕ → M, b 0 = z ∧ (∀ n, b n ∈ V ∩ G) ∧
      ∀ n, map ((backwardNoise path n).val, b (n + 1)) = b n
  capture : ∀ path : ℤ → cube (ι := ι) ε, ∀ b : ℕ → M, (∀ n, b n ∈ V) →
    (∀ n, map ((backwardNoise path n).val, b (n + 1)) = b n) →
      (∀ᶠ n : ℕ in atTop, b n ∈ G) → ∃ j : ℕ, b j ∈ plaque (backwardShift path j)

namespace InverseCubeGeometry
variable {F : Maps (E := E) (ι := ι) T r} {ε : ℝ≥0} {V G : Set M}
  (d : InverseCubeGeometry F ε V G)

def actualMap : M × cube (ι := ι) ε → M := fun z => d.map (z.2.val, z.1)

omit [FiniteDimensional ℝ E] in
theorem continuous_actualMap : Continuous d.actualMap := by
  obtain ⟨O, _hO, hcube, smooth⟩ := d.joint
  exact smooth.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
    (fun z => ⟨hcube z.2.property, mem_univ _⟩)

omit [FiniteDimensional ℝ E] in
theorem zero_map (hε : 0 < ε) (hw : ε ≤ F.window) (y : M) : d.map (0, y) = T.symm y := by
  let a : cube (ι := ι) ε := ⟨0, fun _ => by simp only [Pi.zero_apply, abs_zero]; exact ε.property⟩
  have he := (d.identity a y).self_of_nhds
  change F.family ε 0 (d.map (0, y)) = y at he
  have ht : T (d.map (0, y)) = y := (F.zero_control ε hε hw _).symm.trans he
  exact T.injective (ht.trans (T.apply_symm_apply y).symm)

variable [CompactSpace M]

omit [FiniteDimensional ℝ E] in
def plaqueInputs (source : OpenCubeEndpointContract (E := E) (M := M) (ι := ι))
    (hε : 0 < ε) (hw : ε ≤ F.window) (K : Set M)
    (hV : IsOpen V) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G) :
    LocalPositiveCollar.ForwardCollarPlaqueInputs T.symm d.actualMap V K G := by
  refine {
    zero := ⟨0, fun _ => by simp only [Pi.zero_apply, abs_zero]; exact ε.property⟩
    continuous_noise := d.continuous_actualMap
    zero_noise := d.zero_map hε hw
    local_cover := ?_
    plaque := d.plaque
    lower_semicontinuous := d.lower_semicontinuous
    backward_orbit := d.backward_orbit
    capture := d.capture }
  obtain ⟨δ, hδ, cover⟩ := F.inverse_uniform_control_radius source ε hε hw d.map d.joint d.identity d.spatial
  intro x hx
  have hx' : x ∈ isolatedCore T K := by simpa only [isolatedCore_symm] using hx
  refine ⟨ball x δ ∩ (V ∩ G), isOpen_ball.inter (hV.inter hG),
    ⟨mem_ball_self hδ, hcoreV hx', hcoreG hx'⟩, inter_subset_right, ?_⟩
  intro y hy
  apply cover (T x) y
  simpa only [Homeomorph.symm_apply_apply, mem_ball, dist_comm] using hy.1

end InverseCubeGeometry
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
