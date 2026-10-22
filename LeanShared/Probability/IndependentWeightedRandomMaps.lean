module

public import LeanShared.Probability.WeightedRandomMapKernel
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! Independent actual noise maps factor their weighted and killed kernels.
The state/noise weights are retained; no endpoint density or spectral
factorization is assumed. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace LeanShared.WeightedRandomMapKernel

variable {X X' Y Y' Ω Ω' : Type*}
  [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y] [MeasurableSpace Y']
  [MeasurableSpace Ω] [MeasurableSpace Ω']

def independentWeight (W : X × Ω → ℝ) (W' : X' × Ω' → ℝ) :
    (X × X') × (Ω × Ω') → ℝ := fun z => W (z.1.1, z.2.1) * W' (z.1.2, z.2.2)

def independentMap (F : X × Ω → Y) (F' : X' × Ω' → Y') :
    (X × X') × (Ω × Ω') → Y × Y' := fun z => (F (z.1.1, z.2.1), F' (z.1.2, z.2.2))

theorem independentWeight_measurable {W : X × Ω → ℝ} {W' : X' × Ω' → ℝ}
    (hW : Measurable W) (hW' : Measurable W') : Measurable (independentWeight W W') :=
  (hW.comp (measurable_fst.fst.prodMk measurable_snd.fst)).mul
    (hW'.comp (measurable_fst.snd.prodMk measurable_snd.snd))

theorem independentMap_measurable {F : X × Ω → Y} {F' : X' × Ω' → Y'}
    (hF : Measurable F) (hF' : Measurable F') : Measurable (independentMap F F') :=
  (hF.comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
    (hF'.comp (measurable_fst.snd.prodMk measurable_snd.snd))

/-- Weighting and then drawing two independent maps gives the product of
 their actual weighted transition measures. -/
theorem independent_transition
    (ρ : Measure Ω) (ρ' : Measure Ω') [IsFiniteMeasure ρ] [IsFiniteMeasure ρ']
    (W : X × Ω → ℝ) (W' : X' × Ω' → ℝ) (hW : Measurable W) (hW' : Measurable W')
    (hW0 : ∀ x ω, 0 ≤ W (x, ω))
    (F : X × Ω → Y) (F' : X' × Ω' → Y') (hF : Measurable F) (hF' : Measurable F')
    (x : X) (x' : X') :
    transition (ρ.prod ρ') (independentWeight W W') (independentMap F F') (x, x') =
      (transition ρ W F x).prod (transition ρ' W' F' x') := by
  rw [transition_apply (ρ.prod ρ') _ (independentWeight_measurable hW hW') _
    (independentMap_measurable hF hF'), transition_apply ρ W hW F hF,
    transition_apply ρ' W' hW' F' hF']
  rw [Measure.map_prod_map
    (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω))))
    (ρ'.withDensity (fun ω => ENNReal.ofReal (W' (x', ω))))
    (show Measurable (fun ω => F (x, ω)) from hF.comp measurable_prodMk_left)
    (show Measurable (fun ω => F' (x', ω)) from hF'.comp measurable_prodMk_left)]
  have hd : (ρ.prod ρ').withDensity
      (fun z => ENNReal.ofReal (independentWeight W W' ((x, x'), z))) =
      (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))).prod
        (ρ'.withDensity (fun ω => ENNReal.ofReal (W' (x', ω)))) := by
    rw [prod_withDensity (μ := ρ) (ν := ρ')
      (f := fun ω => ENNReal.ofReal (W (x, ω)))
      (g := fun ω => ENNReal.ofReal (W' (x', ω)))
      (show Measurable (fun ω => ENNReal.ofReal (W (x, ω))) from
        (hW.comp measurable_prodMk_left).ennreal_ofReal)
      (show Measurable (fun ω => ENNReal.ofReal (W' (x', ω))) from
        (hW'.comp measurable_prodMk_left).ennreal_ofReal)]
    congr 1
    funext z
    exact ENNReal.ofReal_mul (hW0 x z.1)
  rw [hd]
  rfl

/-- Killing on the product live set factors as well, including the exact
live indicators. -/
theorem independent_killed
    (ρ : Measure Ω) (ρ' : Measure Ω') [IsFiniteMeasure ρ] [IsFiniteMeasure ρ']
    (W : X × Ω → ℝ) (W' : X' × Ω' → ℝ) (hW : Measurable W) (hW' : Measurable W')
    (hW0 : ∀ x ω, 0 ≤ W (x, ω))
    (F : X × Ω → Y) (F' : X' × Ω' → Y') (hF : Measurable F) (hF' : Measurable F')
    (K : Set Y) (K' : Set Y') (hK : MeasurableSet K) (hK' : MeasurableSet K')
    (x : X) (x' : X') :
    killed (ρ.prod ρ') (independentWeight W W') (independentMap F F')
      (K ×ˢ K') (hK.prod hK') (x, x') =
      (killed ρ W F K hK x).prod (killed ρ' W' F' K' hK' x') := by
  let : IsSFiniteKernel (transition ρ W F) := by unfold transition; infer_instance
  let : IsSFiniteKernel (transition ρ' W' F') := by unfold transition; infer_instance
  change (transition (ρ.prod ρ') (independentWeight W W') (independentMap F F')
    (x, x')).restrict (K ×ˢ K') =
      ((transition ρ W F x).restrict K).prod ((transition ρ' W' F' x').restrict K')
  rw [independent_transition ρ ρ' W W' hW hW' hW0 F F' hF hF']
  exact (Measure.prod_restrict K K').symm

end LeanShared.WeightedRandomMapKernel
