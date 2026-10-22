module

public import ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedNoiseFamily

/-! The stabilizing product gives the literal original stochastic-stability
conclusion. Its ordinary deterministic product limit determines the original
equilibrium marginal, while the same noisy marginal family is retained. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedNoiseStability
open LeanShared RegularNoise ActualStabilizedNoisePoint
variable {X Y E H ι κ : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y] [ChartedSpace E X] [ChartedSpace H Y]
  {T : X ≃ₜ X} {T' : Y ≃ₜ Y} {r : ℝ}
  (P : Maps (E := E) (ι := ι) T r) (Q : Maps (E := H) (ι := κ) T' r)
  (L : Laws (ι := ι)) (L' : Laws (ι := κ))
  (V : Set X) (w : X → ℝ) (hw : Measurable w)
  (RX RY : ℝ) (hRX : 0 < RX) (hRY : 1 ≤ RY) (bound : ∀ x, w x ≤ RX)

local instance stabilizedFamilyCompactUniv : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ
local instance stabilizedFamilyCompactCollar : CompactSpace (closure V) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact
local instance stabilizedFamilyCompactProduct : CompactSpace (closure (Set.prod V (univ : Set Y))) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

/-- The deterministic product limit is projected using the actual closed-state
coordinates; no marginal-limit identity is supplied separately. -/
theorem stability
    (nonnegative : ∀ x, 0 ≤ w x) (Λ : Set X) (hΛ : (closure V ∩ Λ).Nonempty)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδwindow : δ ≤ min P.window Q.window)
    (νY : ℝ≥0 → ProbabilityMeasure (univ : Set Y))
    (ν : ℝ≥0 → ProbabilityMeasure (closure (Set.prod V (univ : Set Y))))
    (ν₀ : ProbabilityMeasure (closure (Set.prod V (univ : Set Y))))
    (limit : Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀))
    (sf : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      HasStrongFellerKernel (original P Q L ε hε (hεδ.trans hδwindow) V w hw RX hRX bound))
    (auxiliary : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      LocalConclusions.NormalizedGap
        (auxiliaryLocal P Q L' ε hε (hεδ.trans hδwindow) RY hRY) univ (νY ε))
    (localPoint : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      LocalConclusions.Point
        (closedProduct P Q L L' ε hε (hεδ.trans hδwindow) V w hw RX RY hRX hRY bound)
        (RX * RY) {z | z.val.1 ∈ Λ} (ν ε))
    (localGap : ∀ ε (hε : 0 < ε) (hεδ : ε ≤ δ),
      LocalConclusions.NormalizedGap
        (closedProduct P Q L L' ε hε (hεδ.trans hδwindow) V w hw RX RY hRX hRY bound)
        {z | z.val.1 ∈ Λ} (ν ε)) (y : Y)
    (potential : X → ℝ) (νeq : ProbabilityMeasure X) (νaux : ProbabilityMeasure Y)
    (productLimit : (ν₀ : Measure (closure (Set.prod V (univ : Set Y)))).map Subtype.val =
      (νeq : Measure X).prod (νaux : Measure Y))
    (equilibrium : ThermodynamicDefinitions.IsEquilibriumState T potential Λ νeq)
    (unique : ∀ ζ : ProbabilityMeasure X,
      ThermodynamicDefinitions.IsEquilibriumState T potential Λ ζ → ζ = νeq) :
    LocalConclusions.Stability P L (closure V) Λ isClosed_closure.measurableSet
      (fun x => w x.val) (hw.comp measurable_subtype_coe) RX hRX
      (fun x => bound x.val) potential := by
  obtain ⟨_, hlimit, hpoints⟩ := ActualStabilizedNoiseFamily.existence_and_limit
    P Q L L' V w hw RX RY hRX hRY bound nonnegative Λ hΛ δ hδ hδwindow
    νY ν ν₀ limit sf auxiliary localPoint localGap y
  let project : closure (Set.prod V (univ : Set Y)) → closure V :=
    fun z => ((LiveProductCoordinates.closedCollar V) z).1
  have hp : Measurable project :=
    (continuous_fst.comp (LiveProductCoordinates.closedCollar V).continuous).measurable
  have hmap : ((ν₀.map project : ProbabilityMeasure (closure V)) : Measure (closure V)).map
      Subtype.val = (νeq : Measure X) := by
    change ((ν₀ : Measure (closure (Set.prod V (univ : Set Y)))).map project).map
      Subtype.val = _
    rw [Measure.map_map measurable_subtype_coe hp]
    have he : (Subtype.val : closure V → X) ∘ project =
        Prod.fst ∘ (Subtype.val : closure (Set.prod V (univ : Set Y)) → X × Y) := rfl
    rw [he, ← Measure.map_map measurable_fst measurable_subtype_coe, productLimit,
      Measure.map_fst_prod, measure_univ, one_smul]
  exact ⟨ν₀.map project, νeq, hmap, equilibrium, unique, δ,
    hδwindow.trans (min_le_left _ _), hδ,
    (fun ε => (ν ε).map project), hlimit, hpoints⟩

end ConditionedStochasticStabilityHyperbolic.Paper.ActualStabilizedNoiseStability
