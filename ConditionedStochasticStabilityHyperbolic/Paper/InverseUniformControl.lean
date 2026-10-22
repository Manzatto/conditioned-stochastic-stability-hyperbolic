module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformControl
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseControlNondegeneracy

/-! The actual inverse perturbation inherits a uniform control-image radius
from forward nondegeneracy and ordinary inverse calculus. -/

@[expose] public noncomputable section
open Set Function Filter Metric IsManifold
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Maps.inverse_uniform_control_radius
    (F : Maps (E := E) (ι := ι) T r)
    (classicalSource : OpenCubeEndpointContract (E := E) (M := M) (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (G : Control (ι := ι) × M → M)
    (joint : ∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1 G (O ×ˢ univ))
    (identity : ∀ (a : cube (ι := ι) ε) (y : M),
      ∀ᶠ p in 𝓝 a.val, F.family ε p (G (p, y)) = y)
    (spatial : ∀ (a : cube (ι := ι) ε) (y : M),
      Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
        (F.family ε a.val) (G (a.val, y)))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : M, dist (T.symm x) y < δ →
      ∃ a : cube (ι := ι) ε, G (a.val, x) = y := by
  have rank : ∀ (a : cube (ι := ι) ε) (y : M),
      Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
        (fun b : Control (ι := ι) => G (b, y)) a.val) := by
    intro a y
    obtain ⟨O, hO, hcube, smooth⟩ := joint
    have hat : ContMDiffAt ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E)))
        (𝓘(ℝ, E)) 1 G (a.val, y) := smooth.contMDiffAt
      ((hO.prod isOpen_univ).mem_nhds ⟨hcube a.property, mem_univ y⟩)
    have hp : ContMDiffAt (𝓘(ℝ, Control (ι := ι)))
        ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) 1
        (fun p : Control (ι := ι) => (p, y)) a.val := contMDiffAt_id.prodMk contMDiffAt_const
    exact F.inverse_control_surjective ε hε hw G a y
      ((hat.comp a.val hp).mdifferentiableAt one_ne_zero) (identity a y) (spatial a y)
  have zero : ∀ y, G (0, y) = T.symm y := by
    intro y
    let a : cube (ι := ι) ε := ⟨0, fun _ => by simp only [Pi.zero_apply, abs_zero]; exact ε.property⟩
    have he := (identity a y).self_of_nhds
    change F.family ε 0 (G (0, y)) = y at he
    have ht : T (G (0, y)) = y :=
      (F.zero_control ε hε hw (G (0, y))).symm.trans he
    exact T.injective (ht.trans (T.apply_symm_apply y).symm)
  have ho := classicalSource ε hε G joint rank
  obtain ⟨δ, hδ, hc⟩ := LeanShared.UniformControlImage.exists_uniform_radius T.symm T.symm.continuous
    (fun z : M × Control (ι := ι) => G (z.2, z.1))
    (interior (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε)) 0
    (zero_interior_cube ε hε) zero ho
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  obtain ⟨a, ha, he⟩ := hc x y hxy
  exact ⟨⟨a, interior_subset ha⟩, he⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
