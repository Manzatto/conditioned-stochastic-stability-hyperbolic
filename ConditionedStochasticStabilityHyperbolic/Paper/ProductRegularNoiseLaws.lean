module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Probability.IndependentNoiseCubes

/-! Independent scale-dependent noise laws satisfy the manuscript's literal
sum-coordinate cube hypotheses. Neither factor is required to be continuous
in the noise scale. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The actual independent law, transported to the single control cube on
`ι ⊕ κ`. Its reference density is ordinary Lebesgue volume on that cube. -/
def productLaws (L : Laws (ι := ι)) (L' : Laws (ι := κ)) : Laws (ι := ι ⊕ κ) where
  law ε := ((L.law ε).prod (L'.law ε)).map (NoiseCubeRescaling.splitCube (ε : ℝ)).symm
  probability ε := by
    let : IsProbabilityMeasure (L.law ε) := L.probability ε
    let : IsProbabilityMeasure (L'.law ε) := L'.probability ε
    infer_instance
  full_support ε hε := by
    let : IsProbabilityMeasure (L.law ε) := L.probability ε
    let : IsProbabilityMeasure (L'.law ε) := L'.probability ε
    let : (L.law ε).IsOpenPosMeasure := L.full_support ε hε
    let : (L'.law ε).IsOpenPosMeasure := L'.full_support ε hε
    exact (NoiseCubeRescaling.splitCube (ε : ℝ)).symm.continuous.isOpenPosMeasure_map
      (NoiseCubeRescaling.splitCube (ε : ℝ)).symm.surjective
  bounded_density ε hε := by
    obtain ⟨p, hp, B, hB, hpB, hL⟩ := L.bounded_density ε hε
    obtain ⟨q, hq, D, hD, hqD, hL'⟩ := L'.bounded_density ε hε
    let e := NoiseCubeRescaling.splitCube (ι := ι) (κ := κ) (ε : ℝ)
    refine ⟨fun v => p (e v).1 * q (e v).2,
      (hp.comp (measurable_fst.comp e.measurable)).mul
        (hq.comp (measurable_snd.comp e.measurable)), B * D,
      ENNReal.mul_ne_top hB hD, fun v => mul_le_mul' (hpB _) (hqD _), ?_⟩
    change (((L.law ε).prod (L'.law ε)).map e.symm) = _
    rw [hL, hL']
    change (((NoiseCubeRescaling.cubeVolume (ι := ι) (ε : ℝ)).withDensity p).prod
      ((NoiseCubeRescaling.cubeVolume (ι := κ) (ε : ℝ)).withDensity q)).map e.symm = _
    rw [prod_withDensity hp hq]
    rw [LeanShared.Homeomorph.map_withDensity e.symm _ (fun z => p z.1 * q z.2)
      ((hp.comp measurable_fst).mul (hq.comp measurable_snd))]
    rw [NoiseCubeRescaling.splitCube_symm_volume]
    rfl

/-- The sum-coordinate law really has the two independent original marginals. -/
theorem productLaws_split (L : Laws (ι := ι)) (L' : Laws (ι := κ)) (ε : ℝ≥0) :
    ((productLaws L L').law ε).map (NoiseCubeRescaling.splitCube (ε : ℝ)) =
      (L.law ε).prod (L'.law ε) := by
  change (((L.law ε).prod (L'.law ε)).map
    (NoiseCubeRescaling.splitCube (ε : ℝ)).symm).map
      (NoiseCubeRescaling.splitCube (ε : ℝ)) = _
  rw [Measure.map_map (NoiseCubeRescaling.splitCube (ε : ℝ)).measurable
    (NoiseCubeRescaling.splitCube (ε : ℝ)).symm.measurable]
  simp only [Function.comp_def, Homeomorph.apply_symm_apply, Measure.map_id']

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
