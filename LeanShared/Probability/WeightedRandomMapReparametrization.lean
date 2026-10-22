module

public import LeanShared.Probability.WeightedRandomMapKernel
public import LeanShared.Probability.IndependentNoiseCubes

/-! Actual state-and-noise weighted kernels are unchanged by an invertible
continuous control reparametrization. This includes the full weight and
killing set, not just the unweighted transition distribution. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace LeanShared.WeightedRandomMapKernel

variable {X Y Ω Ξ : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Ω] [TopologicalSpace Ξ]
  [MeasurableSpace Ω] [MeasurableSpace Ξ] [BorelSpace Ω] [BorelSpace Ξ]

/-- Pulling back the noise law and both actual functions preserves the exact
weighted transition kernel. -/
theorem transition_reparametrization (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) [IsFiniteMeasure ρ]
    (W : X × Ξ → ℝ) (hW : Measurable W) (F : X × Ξ → Y) (hF : Measurable F) :
    transition (ρ.map e.symm) (fun z : X × Ω => W (z.1, e z.2))
      (fun z : X × Ω => F (z.1, e z.2)) = transition ρ W F := by
  ext x : 1
  rw [transition_apply (ρ.map e.symm) (fun z : X × Ω => W (z.1, e z.2))
    (hW.comp (measurable_fst.prodMk (e.measurable.comp measurable_snd)))
    (fun z : X × Ω => F (z.1, e z.2))
    (hF.comp (measurable_fst.prodMk (e.measurable.comp measurable_snd))) x,
    transition_apply ρ W hW F hF]
  have hd : (ρ.map e.symm).withDensity
      (fun ω => ENNReal.ofReal (W (x, e ω))) =
      (ρ.withDensity (fun ξ => ENNReal.ofReal (W (x, ξ)))).map e.symm := by
    simpa only [Function.comp_def, Homeomorph.symm_symm] using
      (LeanShared.Homeomorph.map_withDensity e.symm ρ
        (fun ξ => ENNReal.ofReal (W (x, ξ)))
        ((hW.comp measurable_prodMk_left).ennreal_ofReal)).symm
  rw [hd, Measure.map_map
    (show Measurable (fun ω : Ω => F (x, e ω)) from
      hF.comp (measurable_const.prodMk e.measurable)) e.symm.measurable]
  simp only [Function.comp_def, Homeomorph.apply_symm_apply]

/-- Killing after reparametrization preserves the same live indicator. -/
theorem killed_reparametrization (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) [IsFiniteMeasure ρ]
    (W : X × Ξ → ℝ) (hW : Measurable W) (F : X × Ξ → Y) (hF : Measurable F)
    (K : Set Y) (hK : MeasurableSet K) :
    killed (ρ.map e.symm) (fun z : X × Ω => W (z.1, e z.2))
      (fun z : X × Ω => F (z.1, e z.2)) K hK = killed ρ W F K hK := by
  unfold killed
  rw [transition_reparametrization e ρ W hW F hF]

end LeanShared.WeightedRandomMapKernel
