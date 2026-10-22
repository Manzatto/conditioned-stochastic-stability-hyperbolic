module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductControlGeometry
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductWhitneyAtlas
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! Literal product regular noise geometry. The open parameter extension,
control rank, and finite ordinary atlas are constructed from the original
families, independently of all driving laws. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [Fintype ι] [Fintype κ]
  {T : X ≃ₜ X} {T' : Y ≃ₜ Y} {r : ℝ}

local instance productRegularNoiseMapsLocal1 : ChartedSpace (E × F) (X × Y) := productCharts

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The same actual product chart dictionary also constructs the smooth
manifold structure needed to apply HL to the stabilized system. -/
theorem productManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F)) X Y

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ, E)) ∞ X] [IsManifold (𝓘(ℝ, F)) ∞ Y] in
/-- The open C¹ parameter extension is derived, including every control
on the original closed cube. -/
theorem independentFamily_joint_C1
    (P : Maps (E := E) (ι := ι) T r) (Q : Maps (E := F) (ι := κ) T' r)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ min P.window Q.window) :
    ∃ O : Set (Control (ι := ι ⊕ κ)), IsOpen O ∧
      (LeanShared.NoiseCubeRescaling.cube (ι := ι ⊕ κ) ε : Set (Control (ι := ι ⊕ κ))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι ⊕ κ))).prod (𝓘(ℝ, E × F)))
        (𝓘(ℝ, E × F)) 1
        (fun z : Control (ι := ι ⊕ κ) × (X × Y) => independentFamily P Q ε z.1 z.2)
        (O ×ˢ univ) := by
  obtain ⟨OP, hOP, hcP, hP⟩ := P.joint_C1 ε hε (le_min_iff.mp hw).1
  obtain ⟨OQ, hOQ, hcQ, hQ⟩ := Q.joint_C1 ε hε (le_min_iff.mp hw).2
  let e := splitControl (ι := ι) (κ := κ)
  let O : Set (Control (ι := ι ⊕ κ)) := e ⁻¹' (OP ×ˢ OQ)
  refine ⟨O, (hOP.prod hOQ).preimage e.continuous, ?_, ?_⟩
  · intro v hv
    exact ⟨hcP (fun i => hv (.inl i)), hcQ (fun j => hv (.inr j))⟩
  · simp only [modelWithCornersSelf_prod]
    let L : Control (ι := ι ⊕ κ) →L[ℝ] Control (ι := ι) :=
      (ContinuousLinearMap.fst ℝ _ _).comp e.toContinuousLinearMap
    let R : Control (ι := ι ⊕ κ) →L[ℝ] Control (ι := κ) :=
      (ContinuousLinearMap.snd ℝ _ _).comp e.toContinuousLinearMap
    have hInL : ContMDiff
        ((𝓘(ℝ, Control (ι := ι ⊕ κ))).prod ((𝓘(ℝ, E)).prod (𝓘(ℝ, F))))
        ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) 1
        (fun z : Control (ι := ι ⊕ κ) × (X × Y) => (L z.1, z.2.1)) :=
      (L.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd.fst
    have hInR : ContMDiff
        ((𝓘(ℝ, Control (ι := ι ⊕ κ))).prod ((𝓘(ℝ, E)).prod (𝓘(ℝ, F))))
        ((𝓘(ℝ, Control (ι := κ))).prod (𝓘(ℝ, F))) 1
        (fun z : Control (ι := ι ⊕ κ) × (X × Y) => (R z.1, z.2.2)) :=
      (R.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd.snd
    have hleft := hP.comp hInL.contMDiffOn (show MapsTo
        (fun z : Control (ι := ι ⊕ κ) × (X × Y) => (L z.1, z.2.1))
        (O ×ˢ univ) (OP ×ˢ univ) from fun _ hz => ⟨hz.1.1, mem_univ _⟩)
    have hright := hQ.comp hInR.contMDiffOn (show MapsTo
        (fun z : Control (ι := ι ⊕ κ) × (X × Y) => (R z.1, z.2.2))
        (O ×ˢ univ) (OQ ×ˢ univ) from fun _ hz => ⟨hz.1.2, mem_univ _⟩)
    exact hleft.prodMk hright

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
