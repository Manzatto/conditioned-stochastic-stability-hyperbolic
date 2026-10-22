module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformControl
public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveCollar

/-! The literal perturbation hypotheses construct the zero-control,
continuity and local-cover clauses of the plaque packet. Only the classical
random unstable-plaque geometry is retained as input. -/

@[expose] public noncomputable section
open Set Metric Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared ControlledPlaqueClosure
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
  [MetricSpace Parameters] {T : M ≃ₜ M} {r : ℝ}
  {F : Maps (E := E) (ι := ι) T r} {evaluate : Parameters → M → M}

/-- The three random-manifold clauses independent of noise image balls and
spectral positivity. These are the deferred classical plaque inputs. -/
structure ClassicalPlaqueGeometry (H : M × FixedControl (ι := ι) → M) (V K G : Set M) where
  plaque : (ℤ → FixedControl (ι := ι)) → Set M
  lower_semicontinuous : ∀ ω : ℤ → FixedControl (ι := ι),
    ∀ ωn : ℕ → ℤ → FixedControl (ι := ι), Tendsto ωn atTop (𝓝 ω) →
      ∀ z ∈ plaque ω, ∃ zn : ℕ → M, Tendsto zn atTop (𝓝 z) ∧ ∀ k, zn k ∈ plaque (ωn k)
  backward_orbit : ∀ ω : ℤ → FixedControl (ι := ι), ∀ z ∈ plaque ω,
    ∃ b : ℕ → M, b 0 = z ∧ (∀ n, b n ∈ V ∩ G) ∧
      ∀ n, H (b (n + 1), backwardNoise ω n) = b n
  capture : ∀ ω : ℤ → FixedControl (ι := ι), ∀ b : ℕ → M, (∀ n, b n ∈ V) →
    (∀ n, H (b (n + 1), backwardNoise ω n) = b n) →
      (∀ᶠ n : ℕ in atTop, b n ∈ G) → ∃ j : ℕ, b j ∈ plaque (backwardShift ω j)

omit [FiniteDimensional ℝ E] in
theorem Representation.local_control_cover
    (p : Representation F Parameters evaluate)
    (classicalSource : OpenCubeEndpointContract (E := E) (M := M) (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (V K G : Set M) (hV : IsOpen V) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G) :
    ∀ x ∈ isolatedCore T K, ∃ W : Set M,
      IsOpen W ∧ x ∈ W ∧ W ⊆ V ∩ G ∧ ∀ y ∈ W,
        ∃ z : FixedControl (ι := ι), evaluate (p.fixedParameters ε z) (T.symm x) = y := by
  obtain ⟨δ, hδ, cover⟩ := p.exists_uniform_fixed_control_radius classicalSource ε hε hw
  intro x hx
  refine ⟨ball x δ ∩ (V ∩ G), isOpen_ball.inter (hV.inter hG),
    ⟨mem_ball_self hδ, hcoreV hx, hcoreG hx⟩, inter_subset_right, ?_⟩
  intro y hy
  apply cover (T.symm x) y
  simpa only [Homeomorph.apply_symm_apply, mem_ball, dist_comm] using hy.1

omit [FiniteDimensional ℝ E] in
def Representation.forwardPlaqueInputs
    (p : Representation F Parameters evaluate)
    (classicalSource : OpenCubeEndpointContract (E := E) (M := M) (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (V K G : Set M) (hV : IsOpen V) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (geometry : ClassicalPlaqueGeometry
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) V K G) :
    LocalPositiveCollar.ForwardCollarPlaqueInputs T
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) V K G where
  zero := zeroFixed
  continuous_noise := by
    have eq : (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) =
        (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2) :=
      funext (fun z => p.actual_fixedMap ε hε hw z.1 z.2)
    rw [eq]
    exact F.fixedMap_continuous ε hε (hw.trans p.window_le)
  zero_noise := by
    intro x
    rw [p.actual_fixedMap ε hε hw]
    simp only [Maps.fixedMap, dite_eq_left hε]
    change F.family ε (fun _ => (ε : ℝ) * 0) x = T x
    have hz : (fun _ : ι => (ε : ℝ) * 0) = (0 : Control (ι := ι)) :=
      funext (fun _ => mul_zero _)
    rw [hz]
    exact F.zero_control ε hε (hw.trans p.window_le) x
  local_cover := p.local_control_cover classicalSource ε hε hw V K G hV hG hcoreV hcoreG
  plaque := geometry.plaque
  lower_semicontinuous := geometry.lower_semicontinuous
  backward_orbit := geometry.backward_orbit
  capture := geometry.capture

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
