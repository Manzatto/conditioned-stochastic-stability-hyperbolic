module

public import ConditionedStochasticStabilityHyperbolic.Global.PositiveNoiseContinuation
public import ConditionedStochasticStabilityHyperbolic.Global.LiteralHG2Clauses

/-! The continued analytic interface yields conclusions for the ORIGINAL
literal process. The scale continuation is used only to satisfy
all-positive interfaces; exact window identities remove it from every final
QEM, uniqueness, support, stable-basin and absorption assertion. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.WindowedHG2Application
open AbsorbingMarkovChains LeanShared ShiftedFiltrationGeometry
open PositiveNoiseContinuation DerivedHG2Application
variable {X I Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]
  {T : X ≃ₜ X} {A : Set X} {hA : IsOpen A} {Λ : I → Set X} {ℓ : ℕ}
  {D : AdaptedSource T A Λ ℓ} {t : ℕ} {terminal : Fin t → Fin ℓ}
  {root : ∀ s, Fin ((terminal s).val + 1)}
  {C : NNReal → CanonicalChain X} {window : NNReal}
  (g : WindowedGeometry (Ω := Ω) T A hA Λ ℓ D t terminal root C window)

/-- The original noise law and original maps at the original scale. -/
def literalProcess (ε : NNReal) : CanonicalChain ↥(Aᶜ) := by
  let : IsProbabilityMeasure (g.noise ε) := g.probability ε
  exact RestrictedNoise.chain (g.noise ε) (g.maps ε) (g.measurable ε) Aᶜ hA.measurableSet.compl
    (fun x : ↥(Aᶜ) => Real.exp (g.potential x.val))
    ((Real.measurable_exp.comp g.potential_measurable).comp measurable_subtype_coe)
    g.R g.R_positive (fun x => g.weight_bound x.val)

omit [CompactSpace X] in
theorem continued_literal (hw : 0 < window) (ε : NNReal) :
    DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root
      (PositiveNoiseContinuation.chain C window) (g.continued hw) ε =
      literalProcess g (scale window ε) := rfl

omit [CompactSpace X] in
theorem continued_literal_eq (hw : 0 < window) (ε : NNReal) (hε : ε ≤ window) :
    DerivedHG2Conclusions.literalChain T A hA Λ ℓ D t terminal root
      (PositiveNoiseContinuation.chain C window) (g.continued hw) ε = literalProcess g ε :=
  (continued_literal g hw ε).trans (congrArg (literalProcess g) (scale_eq hε))

theorem literal_conclusions_from_continued_family
    (hw : 0 < window)
    (sf : ∀ ε, 0 < ε → ε ≤ window → HasStrongFellerKernel (C ε))
    (d : Families T A hA Λ ℓ D t terminal root
      (PositiveNoiseContinuation.chain C window) (strongFeller C window hw sf))
    (hℓ : 0 < ℓ) (c : ℝ) (hc : 0 ≤ c)
    (bound : ∀ ε, 0 < ε → ε ≤ window → ∀ x z,
      dist (g.maps ε (x, z)) (T x) ≤ c * (ε : ℝ)) :
    ∃ ν : Fin t → NNReal → ProbabilityMeasure ↥(Aᶜ),
      ∃ δ : NNReal, 0 < δ ∧
        LiteralHG2Clauses.Clauses T A Λ ℓ D t terminal root
          (literalProcess g) g.maps ν d.equilibrium δ := by
  have hd := DerivedHG2Conclusions.conditional_global_global
    T A hA Λ ℓ D t terminal root (PositiveNoiseContinuation.chain C window)
    (strongFeller C window hw sf) d (g.continued hw) hℓ c hc
    (g.continued_noise_bound hw c hc bound)
  obtain ⟨δ, hδ, clauses⟩ := hd
  let ν := liveLaw T A hA Λ ℓ D t terminal root
    (PositiveNoiseContinuation.chain C window) (strongFeller C window hw sf) d
  have actual := LiteralHG2Clauses.of_derived
    (PositiveNoiseContinuation.chain C window) (strongFeller C window hw sf) d (g.continued hw) clauses
  refine ⟨ν, min δ window, lt_min hδ hw, ?_⟩
  exact actual.transfer_window hw (continued_literal_eq g hw)
    (fun ε hε => congrArg g.maps (scale_eq hε))

end ConditionedStochasticStabilityHyperbolic.Global.WindowedHG2Application
