module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelUniformBounds
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImageClipped

/-! Block bounds for words of literal letters give the block field for the
clipped letter family on a fixed control space: positive scales use the
rescaled controls, and scale zero uses the zero-control letter. -/
@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelLetterBlocks
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
open Paper.RegularNoise.WordLists

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem block_of_words (j : m.StrongSpace →L[ℂ] W) (hj : ∀ x, ‖j x‖ = ‖m.inclusionW x‖)
    {Z : Type*} (Ctrl : ℝ≥0 → Type*) (η : ℝ≥0) (hη : 0 < η)
    (letterF : ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → Ctrl ε → Ω)
    (resc : ∀ ε : ℝ≥0, 0 < ε → Z → Ctrl ε) (zeroC : Ctrl η)
    (G : ℝ≥0 → Z → Ω) (hG : ∀ ε hp hl z, G ε z = letterF ε hp hl (resc ε hp z))
    (hG0 : ∀ z, G 0 z = letterF η hη le_rfl zeroC) (N : ℕ) (ρ B : ℝ)
    (words : ∀ ε hp hl (control : Fin N → Ctrl ε),
      WordBound m (List.ofFn fun k => letterF ε hp hl (control k)) (ρ ^ N) B) :
    ∀ ε ≤ η, ∀ word : List Z, word.length = N → ∀ x,
      ‖FiniteBlockAnnealedEstimates.listWord (fun z => m.generator (G ε z)) word x‖ ≤
        ρ ^ N * ‖x‖ + B * ‖j x‖ := by
  intro ε hε word hlen x
  have target : ∃ letters : Fin N → Ω,
      (fun k : Fin N => G ε (word.get (Fin.cast hlen.symm k))) = letters ∧
      WordBound m (List.ofFn letters) (ρ ^ N) B := by
    by_cases hp : 0 < ε
    · exact ⟨_, funext fun k => hG ε hp hε _,
        words ε hp hε (fun k => resc ε hp (word.get (Fin.cast hlen.symm k)))⟩
    · have zero : ε = 0 := le_antisymm (not_lt.mp hp) zero_le
      subst zero
      exact ⟨_, funext fun k => hG0 _, words η hη le_rfl (fun _ => zeroC)⟩
  obtain ⟨letters, same, bound⟩ := target
  have base : FiniteBlockAnnealedEstimates.listWord (fun z => m.generator (G ε z)) word =
      FiniteBlockAnnealedEstimates.listWord m.generator (List.ofFn letters) :=
    (listWord_map m.generator (G ε) word).trans
      (congrArg _ ((map_eq_ofFn (G ε) word hlen).trans (congrArg List.ofFn same)))
  calc ‖FiniteBlockAnnealedEstimates.listWord (fun z => m.generator (G ε z)) word x‖
      = ‖FiniteBlockAnnealedEstimates.listWord m.generator (List.ofFn letters) x‖ :=
        congrArg (fun L : m.StrongSpace →L[ℂ] m.StrongSpace => ‖L x‖) base
    _ ≤ ρ ^ N * ‖x‖ + B * ‖m.inclusionW x‖ := bound x
    _ = ρ ^ N * ‖x‖ + B * ‖j x‖ := congrArg (fun t => ρ ^ N * ‖x‖ + B * t) (hj x).symm

end ConditionedStochasticStabilityHyperbolic.PhysicalModelLetterBlocks
