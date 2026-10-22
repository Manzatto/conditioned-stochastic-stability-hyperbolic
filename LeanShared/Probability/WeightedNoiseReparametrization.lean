module

public import LeanShared.Probability.WeightedRandomMapIntegrals
public import LeanShared.Probability.NoiseCubeRescaling

/-! Exact fixed-cube transport of the actual inverse/Jacobian kernel.
Both state-and-noise weight and map are reparametrized; no noise-law
continuity or density differentiability is assumed. -/

public noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace LeanShared.WeightedRandomMapKernel
variable {X Y Ω Ξ : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Ω] [TopologicalSpace Ξ] [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [BorelSpace Ω] [BorelSpace Ξ]

 theorem transition_fixedLaw (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) [IsFiniteMeasure ρ]
    (W : X × Ξ → ℝ) (hW : Measurable W) (F : X × Ξ → Y) (hF : Measurable F) :
    transition (NoiseCubeRescaling.fixedLaw e ρ)
      (fun p : X × Ω => W (p.1, e p.2)) (fun p : X × Ω => F (p.1, e p.2)) =
      transition ρ W F := by
  have hm : Measurable (fun p : X × Ω => (p.1, e p.2)) :=
    measurable_fst.prodMk (e.measurable.comp measurable_snd)
  have hWr : Measurable (fun p : X × Ω => W (p.1, e p.2)) := hW.comp hm
  have hFr : Measurable (fun p : X × Ω => F (p.1, e p.2)) := hF.comp hm
  ext x : 1
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  rw [lintegral_transition (NoiseCubeRescaling.fixedLaw e ρ)
      (fun p : X × Ω => W (p.1, e p.2)) hWr (fun p : X × Ω => F (p.1, e p.2)) hFr f hf,
    lintegral_transition ρ W hW F hF f hf]
  change (∫⁻ ω : Ω, ENNReal.ofReal (W (x, e ω)) * f (F (x, e ω)) ∂ρ.map e.symm) = _
  have hi : Measurable (fun ω : Ω => ENNReal.ofReal (W (x, e ω)) * f (F (x, e ω))) :=
    ((hW.comp (measurable_const.prodMk e.measurable)).ennreal_ofReal).mul
      (hf.comp (hF.comp (measurable_const.prodMk e.measurable)))
  rw [lintegral_map hi e.symm.measurable]
  simp only [e.apply_symm_apply]

 theorem killed_fixedLaw (e : Ω ≃ₜ Ξ) (ρ : Measure Ξ) [IsFiniteMeasure ρ]
    (W : X × Ξ → ℝ) (hW : Measurable W) (F : X × Ξ → Y) (hF : Measurable F)
    (K : Set Y) (hK : MeasurableSet K) :
    killed (NoiseCubeRescaling.fixedLaw e ρ)
      (fun p : X × Ω => W (p.1, e p.2)) (fun p : X × Ω => F (p.1, e p.2)) K hK =
      killed ρ W F K hK := by
  unfold killed
  rw [transition_fixedLaw e ρ W hW F hF]

end LeanShared.WeightedRandomMapKernel
