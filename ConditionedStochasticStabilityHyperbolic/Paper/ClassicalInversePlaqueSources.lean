module

public import ConditionedStochasticStabilityHyperbolic.Paper.InverseCubeGeometry
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoisePlaqueCover
public import ConditionedStochasticStabilityHyperbolic.Spectral.CollarPlaqueCapture

/-! The finite capture clause follows from the ordinary local unstable-set
characterization. It need not be supplied as a separate cited conclusion. -/

@[expose] public noncomputable section
open Set Function Filter IsManifold
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared ControlledPlaqueClosure LocalPositiveCollar
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {ε : ℝ≥0} {V G : Set M}

def InverseCubeGeometry.of_local_backward
    (H : Control (ι := ι) × M → M)
    (joint : ∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1 H (O ×ˢ univ))
    (identity : ∀ (a : cube (ι := ι) ε) (y : M),
      ∀ᶠ z in 𝓝 a.val, F.family ε z (H (z, y)) = y)
    (spatial : ∀ (a : cube (ι := ι) ε) (y : M),
      Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (F.family ε a.val) (H (a.val, y))))
    (plaque : (ℤ → cube (ι := ι) ε) → Set M)
    (lower : ∀ path : ℤ → cube (ι := ι) ε,
      ∀ paths : ℕ → ℤ → cube (ι := ι) ε, Tendsto paths atTop (𝓝 path) →
        ∀ z ∈ plaque path, ∃ zn : ℕ → M, Tendsto zn atTop (𝓝 z) ∧
          ∀ k, zn k ∈ plaque (paths k))
    (backward : ∀ path : ℤ → cube (ι := ι) ε, ∀ z ∈ plaque path,
      ∃ b : ℕ → M, b 0 = z ∧ (∀ n, b n ∈ V ∩ G) ∧
        ∀ n, H ((backwardNoise path n).val, b (n + 1)) = b n)
    (local_backward : ∀ (path : ℤ → cube (ι := ι) ε) (b : ℕ → M),
      (∀ n, b n ∈ G) →
      (∀ n, H ((backwardNoise path n).val, b (n + 1)) = b n) → b 0 ∈ plaque path) :
    InverseCubeGeometry F ε V G where
  map := H
  joint := joint
  identity := identity
  spatial := spatial
  plaque := plaque
  lower_semicontinuous := lower
  backward_orbit := backward
  capture := fun path b _ step tail => capture_of_local_backward_characterization
    (fun z : M × cube (ι := ι) ε => H (z.2.val, z.1)) G plaque local_backward path b step tail


def ClassicalPlaqueGeometry.of_local_backward
    (H : M × FixedControl (ι := ι) → M) (K : Set M)
    (plaque : (ℤ → FixedControl (ι := ι)) → Set M)
    (lower : ∀ path : ℤ → FixedControl (ι := ι),
      ∀ paths : ℕ → ℤ → FixedControl (ι := ι), Tendsto paths atTop (𝓝 path) →
        ∀ z ∈ plaque path, ∃ zn : ℕ → M, Tendsto zn atTop (𝓝 z) ∧
          ∀ k, zn k ∈ plaque (paths k))
    (backward : ∀ path : ℤ → FixedControl (ι := ι), ∀ z ∈ plaque path,
      ∃ b : ℕ → M, b 0 = z ∧ (∀ n, b n ∈ V ∩ G) ∧
        ∀ n, H (b (n + 1), backwardNoise path n) = b n)
    (local_backward : ∀ (path : ℤ → FixedControl (ι := ι)) (b : ℕ → M),
      (∀ n, b n ∈ G) →
      (∀ n, H (b (n + 1), backwardNoise path n) = b n) → b 0 ∈ plaque path) :
    ClassicalPlaqueGeometry H V K G where
  plaque := plaque
  lower_semicontinuous := lower
  backward_orbit := backward
  capture := fun path b _ step tail => capture_of_local_backward_characterization
    H G plaque local_backward path b step tail

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
