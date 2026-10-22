module

public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedNoiseStrongFeller

/-! The ordinary smooth-density rank-chart theorem, stated independently of
any stochastic stability conclusion. The literal perturbation's joint C¹ and
control-surjectivity hypotheses instantiate it; the actual law is then handled
by the proved L¹ approximation and exact cube transport. -/

@[expose] public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M]

/-- Classical parametric submersion smoothing for a fixed smooth control
 density, before choosing a noise law. No spectral assertion is included. -/
def SmoothCubeSubmersionContract : Prop :=
  ∀ (ε : ℝ≥0), 0 < ε → ∀ (H : Control (ι := ι) × M → M),
    (∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1 H (O ×ˢ univ)) →
    (∀ (a : cube (ι := ι) ε) (x : M),
      Function.Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
        (fun b : Control (ι := ι) => H (b, x)) a.val)) →
    ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
    ∀ f : M → ℝ, Measurable f → (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) →
      Continuous (fun x => ∫ z : cube (ι := ι) ε, g z.val * f (H (z.val, x)) ∂cubeVolume ε)

variable {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Maps.strongFeller_from_submersion
    (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (classicalSource : SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window) :
    RestrictedStrongFeller.HasStrongFellerNoise (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hw) :=
  F.strongFeller_raw_cube L ε hε hw
    (classicalSource ε hε (fun z => F.family ε z.1 z.2)
      (F.joint_C1 ε hε hw) (F.control_surjective ε hε hw))

omit [FiniteDimensional ℝ E] in
theorem Representation.strongFeller_from_submersion
    {Parameters : Type*} [MetricSpace Parameters] {evaluate : Parameters → M → M}
    {F : Maps (E := E) (ι := ι) T r} (p : Representation F Parameters evaluate)
    (L : Laws (ι := ι))
    (classicalSource : SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (hF : Measurable (fun z : M × FixedControl (ι := ι) =>
      evaluate (p.fixedParameters ε z.2) z.1)) :
    RestrictedStrongFeller.HasStrongFellerNoise (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) hF :=
  p.strongFeller_fixed_cube L ε hε hw hF
    (classicalSource ε hε (fun z => F.family ε z.1 z.2)
      (F.joint_C1 ε hε (hw.trans p.window_le))
      (F.control_surjective ε hε (hw.trans p.window_le)))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
