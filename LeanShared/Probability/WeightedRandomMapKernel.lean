module

public import LeanShared.Probability.RandomMapKernel
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Random-map kernels with noise-dependent weights

The inverse transfer in the support argument has a Jacobian weight depending
on both the state and the noise parameter. This construction weights the
actual noise law before pushing it forward; it does not replace that weight
by a function of the departure state or assume a density on the endpoint.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LeanShared.WeightedRandomMapKernel

variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsFiniteMeasure ρ] (W : X × Ω → ℝ) (hW : Measurable W)

def noise : Kernel X Ω :=
  (Kernel.const X ρ).withDensity (fun x ω => ENNReal.ofReal (W (x, ω)))

include hW in
theorem noise_apply (x : X) :
    noise ρ W x = ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω))) :=
  Kernel.withDensity_apply _ hW.ennreal_ofReal x

instance noise_sfinite : IsSFiniteKernel (noise ρ W) :=
  Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _
    (fun _ _ => ENNReal.ofReal_ne_top)

def transition (F : X × Ω → Y) : Kernel X Y := (Kernel.id ×ₖ noise ρ W).map F

include hW in
theorem transition_apply (F : X × Ω → Y) (hF : Measurable F) (x : X) :
    transition ρ W F x =
      (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))).map (fun ω => F (x, ω)) := by
  ext S hS
  have hFx : Measurable (fun ω => F (x, ω)) := hF.comp measurable_prodMk_left
  rw [transition, Kernel.map_apply _ hF, Measure.map_apply hF hS,
    Kernel.id_prod_apply' _ _ (hS.preimage hF),
    Measure.map_apply hFx hS, noise_apply ρ W hW]
  rfl

include hW in
/-- Actual integration over the original noise parameter with the full
state-and-noise weight. Totalized Bochner integrals are preserved. -/
theorem integral_transition (F : X × Ω → Y) (hF : Measurable F)
    (hW0 : ∀ x ω, 0 ≤ W (x, ω)) (f : Y → ℝ) (hf : Measurable f) (x : X) :
    (∫ y, f y ∂transition ρ W F x) = ∫ ω, W (x, ω) * f (F (x, ω)) ∂ρ := by
  have hFx : Measurable (fun ω => F (x, ω)) := hF.comp measurable_prodMk_left
  have hWx : Measurable (fun ω => W (x, ω)) := hW.comp measurable_prodMk_left
  rw [transition_apply ρ W hW F hF x,
    integral_map_of_stronglyMeasurable hFx hf.stronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      hWx.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hW0 x ω), smul_eq_mul]

def killed (F : X × Ω → Y) (K : Set Y) (hK : MeasurableSet K) : Kernel X Y :=
  (transition ρ W F).restrict hK

include hW in
theorem integral_killed (F : X × Ω → Y) (hF : Measurable F)
    (hW0 : ∀ x ω, 0 ≤ W (x, ω)) (K : Set Y) (hK : MeasurableSet K)
    (f : Y → ℝ) (hf : Measurable f) (x : X) :
    (∫ y, f y ∂killed ρ W F K hK x) =
      ∫ ω, W (x, ω) * K.indicator f (F (x, ω)) ∂ρ := by
  change (∫ y, f y ∂(transition ρ W F x).restrict K) = _
  rw [← integral_indicator hK]
  exact integral_transition ρ W hW F hF hW0 _ (hf.indicator hK) x

/-- A uniform upper weight bound makes the constructed noise kernel finite. -/
theorem noise_isFinite (B : ℝ) (hB : ∀ x ω, W (x, ω) ≤ B) :
    IsFiniteKernel (noise ρ W) :=
  Kernel.isFiniteKernel_withDensity_of_bounded _ ENNReal.ofReal_ne_top
    (fun x ω => ENNReal.ofReal_le_ofReal (hB x ω))

theorem transition_isFinite (F : X × Ω → Y) (B : ℝ)
    (hB : ∀ x ω, W (x, ω) ≤ B) : IsFiniteKernel (transition ρ W F) := by
  let : IsFiniteKernel (noise ρ W) := noise_isFinite ρ W B hB
  unfold transition
  infer_instance

theorem killed_isFinite (F : X × Ω → Y) (K : Set Y) (hK : MeasurableSet K)
    (B : ℝ) (hB : ∀ x ω, W (x, ω) ≤ B) : IsFiniteKernel (killed ρ W F K hK) := by
  let : IsFiniteKernel (transition ρ W F) := transition_isFinite ρ W F B hB
  unfold killed
  infer_instance

include hW in
theorem weighted_noise_isFinite (B : ℝ) (hB : ∀ x ω, W (x, ω) ≤ B) (x : X) :
    IsFiniteMeasure (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))) := by
  let : IsFiniteKernel (noise ρ W) := noise_isFinite ρ W B hB
  rw [← noise_apply ρ W hW x]
  infer_instance

include hW in
omit [IsFiniteMeasure ρ] in
/-- Positive noise-dependent weights preserve full support of the noise law. -/
theorem weighted_noise_isOpenPos [TopologicalSpace Ω] [ρ.IsOpenPosMeasure]
    (hpos : ∀ x ω, 0 < W (x, ω)) (x : X) :
    (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))).IsOpenPosMeasure := by
  constructor
  intro V hV hne hz
  have hWx : Measurable (fun ω => W (x, ω)) := hW.comp measurable_prodMk_left
  have he := (withDensity_apply_eq_zero hWx.ennreal_ofReal).mp hz
  have hs : {ω | ENNReal.ofReal (W (x, ω)) ≠ 0} = univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact ENNReal.ofReal_ne_zero_iff.mpr (hpos x ω)
  rw [hs, univ_inter] at he
  exact (hV.measure_pos ρ hne).ne' he

end LeanShared.WeightedRandomMapKernel
