module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Geometry.ParametricInverseManifoldDerivative

/-! Literal forward noise nondegeneracy supplies inverse noise
nondegeneracy. Only ordinary differentiability of the actual inverse family
and the spatial local-diffeomorphism condition are calculus inputs. -/

@[expose] public noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Maps.inverse_control_surjective
    (F : Maps (E := E) (ι := ι) T r)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (G : Control (ι := ι) × M → M) (a : cube (ι := ι) ε) (y : M)
    (hG : MDifferentiableAt (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
      (fun p => G (p, y)) a.val)
    (identity : ∀ᶠ p in 𝓝 a.val, F.family ε p (G (p, y)) = y)
    (spatial : Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (F.family ε a.val) (G (a.val, y)))) :
    Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
      (fun p => G (p, y)) a.val) := by
  obtain ⟨O, hO, hcube, smooth⟩ := F.joint_C1 ε hε hw
  have atPoint : O ×ˢ (univ : Set M) ∈ 𝓝 (a.val, G (a.val, y)) :=
    (hO.prod isOpen_univ).mem_nhds ⟨hcube a.property, mem_univ _⟩
  have forward := (smooth.contMDiffAt atPoint).mdifferentiableAt one_ne_zero
  exact ParametricInverseManifoldDerivative.inverse_control_surjective
    (fun z : Control (ι := ι) × M => F.family ε z.1 z.2) G a.val y
    forward hG identity spatial (F.control_surjective ε hε hw a (G (a.val, y)))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
