module

public import ConditionedStochasticStabilityHyperbolic.Paper.SmoothSubmersionSource
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseControlNondegeneracy

/-! The forward control rank in the literal noise assumptions supplies the
inverse rank. The same ordinary smooth-density submersion theorem therefore
applies to the actual inverse family; inverse nondegeneracy is not an extra
noise assumption. -/

@[expose] public noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace M] in
theorem Maps.inverse_smooth_density_source
    (F : Maps (E := E) (ι := ι) T r)
    (classicalSource : SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι))
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
    ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
    ∀ f : M → ℝ, Measurable f → (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) →
      Continuous (fun x => ∫ z : cube (ι := ι) ε,
        g z.val * f (G (z.val, x)) ∂cubeVolume ε) := by
  apply classicalSource ε hε G joint
  intro a y
  obtain ⟨O, hO, hcube, smooth⟩ := joint
  have hat : ContMDiffAt ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E)))
      (𝓘(ℝ, E)) 1 G (a.val, y) := smooth.contMDiffAt
    ((hO.prod isOpen_univ).mem_nhds ⟨hcube a.property, mem_univ y⟩)
  have hp : ContMDiffAt (𝓘(ℝ, Control (ι := ι)))
      ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) 1
      (fun p : Control (ι := ι) => (p, y)) a.val :=
    contMDiffAt_id.prodMk contMDiffAt_const
  exact F.inverse_control_surjective ε hε hw G a y
    ((hat.comp a.val hp).mdifferentiableAt one_ne_zero) (identity a y) (spatial a y)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
