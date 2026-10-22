module
public import LeanShared.Probability.IndependentNoiseCubes
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Normalized literal Lebesgue volume on the actual finite control cube,
including a separate Dirac law at scale zero. -/
public noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal Topology
namespace LeanShared.NoiseCubeRescaling
variable {ι : Type*} [Fintype ι]

theorem cube_eq_closedBall {ε : ℝ} (nonnegative : 0 ≤ ε) :
    cube (ι := ι) ε = Metric.closedBall (0 : ι → ℝ) ε := by
  ext v
  simp only [cube, mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg nonnegative, Real.norm_eq_abs]

theorem cubeVolume_openPos {ε : ℝ} (positive : 0 < ε) :
    (cubeVolume (ι := ι) ε).IsOpenPosMeasure := by
  constructor
  intro U openU nonemptyU
  rw [cubeVolume, (MeasurableEmbedding.subtype_coe (cube_compact ε).measurableSet).comap_apply]
  obtain ⟨A, openA, equal⟩ := isOpen_induced_iff.mp openU
  obtain ⟨x, hx⟩ := nonemptyU
  have hxA : x.val ∈ A := by
    change x ∈ (Subtype.val : cube (ι := ι) ε → ι → ℝ) ⁻¹' A
    rwa [equal]
  have hxClosure : x.val ∈ closure (Metric.ball (0 : ι → ℝ) ε) := by
    rw [closure_ball _ positive.ne', ← cube_eq_closedBall positive.le]
    exact x.property
  have meets := mem_closure_iff.mp hxClosure A openA hxA
  have nonempty : (A ∩ Metric.ball (0 : ι → ℝ) ε).Nonempty := by
    simpa only [inter_comm] using meets
  have pos := (openA.inter Metric.isOpen_ball).measure_pos
    (volume : Measure (ι → ℝ)) nonempty
  apply (pos.trans_le (measure_mono ?_)).ne'
  intro y hy
  have live : y ∈ cube (ι := ι) ε := by
    rw [cube_eq_closedBall positive.le]
    exact Metric.ball_subset_closedBall hy.2
  refine ⟨⟨y, live⟩, ?_, rfl⟩
  rw [← equal]
  exact hy.1

@[expose] def zeroControl (ε : ℝ≥0) : cube (ι := ι) ε :=
  ⟨0, fun _ => by
    change |(0 : ℝ)| ≤ (ε : ℝ)
    rw [abs_zero]
    exact ε.property⟩

@[expose] def uniformCubeLaw (ε : ℝ≥0) : Measure (cube (ι := ι) ε) :=
  if 0 < ε then ((cubeVolume (ι := ι) ε) univ)⁻¹ • cubeVolume ε
  else Measure.dirac (zeroControl ε)

theorem uniformCubeLaw_probability (ε : ℝ≥0) :
    IsProbabilityMeasure (uniformCubeLaw (ι := ι) ε) := by
  by_cases positive : 0 < ε
  · let : (cubeVolume (ι := ι) ε).IsOpenPosMeasure := cubeVolume_openPos positive
    let : Nonempty (cube (ι := ι) ε) := ⟨zeroControl ε⟩
    simp only [uniformCubeLaw, ite_eq_left positive]
    infer_instance
  · simp only [uniformCubeLaw, ite_eq_right positive]
    infer_instance

theorem uniformCubeLaw_openPos (ε : ℝ≥0) (positive : 0 < ε) :
    (uniformCubeLaw (ι := ι) ε).IsOpenPosMeasure := by
  let : (cubeVolume (ι := ι) ε).IsOpenPosMeasure := cubeVolume_openPos positive
  let : Nonempty (cube (ι := ι) ε) := ⟨zeroControl ε⟩
  simp only [uniformCubeLaw, ite_eq_left positive]
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

theorem uniformCubeLaw_density (ε : ℝ≥0) (positive : 0 < ε) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ uniformCubeLaw (ι := ι) ε =
      (cubeVolume ε).withDensity (fun _ => c) := by
  let : (cubeVolume (ι := ι) ε).IsOpenPosMeasure := cubeVolume_openPos positive
  let : Nonempty (cube (ι := ι) ε) := ⟨zeroControl ε⟩
  refine ⟨((cubeVolume (ι := ι) ε) univ)⁻¹, ?_, ?_⟩
  · exact ENNReal.inv_ne_top.mpr (Measure.measure_univ_ne_zero.mpr (NeZero.ne _))
  · simp only [uniformCubeLaw, ite_eq_left positive, withDensity_const]

end LeanShared.NoiseCubeRescaling
