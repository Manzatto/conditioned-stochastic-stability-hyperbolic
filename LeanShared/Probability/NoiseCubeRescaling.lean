module

public import LeanShared.Probability.RandomMapKernel
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Analysis.Normed.Group.Constructions

/-! # A fixed noise type for shrinking cubes

Positive-radius cubes are homeomorphic to the unit cube. Pulling each noise
law back separately preserves its full support and the actual transition
kernel; no continuity of the family of laws is required.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace LeanShared.NoiseCubeRescaling

variable {ι : Type*}
def cube (ε : ℝ) := {ω : ι → ℝ | ∀ i, |ω i| ≤ ε}

theorem cube_compact (ε : ℝ) : IsCompact (cube (ι := ι) ε) := by
  have hc := isCompact_pi_infinite (fun _ : ι => isCompact_Icc (a := -ε) (b := ε))
  simpa only [cube, mem_Icc, ← abs_le] using hc

instance cube_compactSpace (ε : ℝ) : CompactSpace (cube (ι := ι) ε) :=
  isCompact_iff_compactSpace.mp (cube_compact ε)

theorem cube_norm_le [Fintype ι] (ε : ℝ) (hε : 0 ≤ ε) (ω : cube (ι := ι) ε) :
    ‖ω.val‖ ≤ ε := by
  exact (pi_norm_le_iff_of_nonneg hε).mpr (fun i => by simpa only [Real.norm_eq_abs] using ω.property i)


/-- The paper's uniform linear Whitney estimate becomes a scale bound on
all rescaled parameters, before choosing a probability law. -/
theorem cube_error_le [Fintype ι] (ε C : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (error : cube (ι := ι) ε → ℝ)
    (herror : ∀ ω, error ω ≤ C * ‖ω.val‖) : ∀ ω, error ω ≤ C * ε := by
  intro ω
  exact (herror ω).trans (mul_le_mul_of_nonneg_left (cube_norm_le ε hε ω) hC)


def rescale (ε : ℝ) (hε : 0 < ε) : cube (ι := ι) 1 ≃ₜ cube (ι := ι) ε where
  toFun ω := ⟨fun i => ε * ω.val i, fun i => by
    rw [abs_mul, abs_of_pos hε]
    simpa using mul_le_mul_of_nonneg_left (ω.property i) hε.le⟩
  invFun ω := ⟨fun i => ε⁻¹ * ω.val i, fun i => by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
    simpa [ne_of_gt hε] using mul_le_mul_of_nonneg_left (ω.property i) (inv_nonneg.mpr hε.le)⟩
  left_inv ω := by ext i; change ε⁻¹ * (ε * ω.val i) = ω.val i; field_simp
  right_inv ω := by ext i; change ε * (ε⁻¹ * ω.val i) = ω.val i; field_simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_const.mul
      ((continuous_apply i).comp (continuous_subtype_val : Continuous (fun ω : cube (ι := ι) 1 => ω.val)))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => continuous_const.mul
      ((continuous_apply i).comp (continuous_subtype_val : Continuous (fun ω : cube (ι := ι) ε => ω.val)))


variable {Ω Ξ X Y : Type*} [TopologicalSpace Ω] [TopologicalSpace Ξ]
  [MeasurableSpace Ω] [MeasurableSpace Ξ] [BorelSpace Ω] [BorelSpace Ξ]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- The law on the fixed parameter space, constructed separately at each
positive noise radius. -/
def fixedLaw (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) : Measure Ω := ρ.map e.symm

instance fixedLaw_finite (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (fixedLaw e ρ) := by
  unfold fixedLaw
  infer_instance

instance fixedLaw_probability (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (fixedLaw e ρ) := by
  unfold fixedLaw
  infer_instance

instance fixedLaw_openPos (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) [ρ.IsOpenPosMeasure] :
    (fixedLaw e ρ).IsOpenPosMeasure :=
  e.symm.continuous.isOpenPosMeasure_map e.symm.surjective

/-- Reparametrization gives exactly the original one-step kernel. All finite
path laws and killed-chain constructions therefore use the same transition. -/
theorem transition_fixedLaw (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) [IsFiniteMeasure ρ]
    (F : X × Ξ → Y) (hF : Measurable F) :
    RandomMapKernel.transition (fixedLaw e ρ) (fun p : X × Ω => F (p.1, e p.2))
      (hF.comp (measurable_fst.prodMk (e.measurable.comp measurable_snd))) =
    RandomMapKernel.transition ρ F hF := by
  ext x : 1
  change (ρ.map e.symm).map (fun ω => F (x, e ω)) = ρ.map (fun ω => F (x, ω))
  have hm : Measurable (fun ω : Ω => F (x, e ω)) :=
    (hF.comp (measurable_const.prodMk e.measurable))
  rw [Measure.map_map hm e.symm.measurable]
  simp only [Function.comp_def, e.apply_symm_apply]

theorem killed_fixedLaw (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) [IsFiniteMeasure ρ]
    (F : X × Ξ → Y) (hF : Measurable F) (K : Set Y) (hK : MeasurableSet K) :
    RandomMapKernel.killed (fixedLaw e ρ) (fun p : X × Ω => F (p.1, e p.2))
      (hF.comp (measurable_fst.prodMk (e.measurable.comp measurable_snd))) K hK =
    RandomMapKernel.killed ρ F hF K hK := by
  unfold RandomMapKernel.killed
  rw [transition_fixedLaw]


end LeanShared.NoiseCubeRescaling
