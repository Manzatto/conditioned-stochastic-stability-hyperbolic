module
public import ConditionedStochasticStabilityHyperbolic.Paper.ControlSubmersionSources
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductRegularNoiseLaws

/-! Original noise rows inherit product-reference null sets by independence.
No original reference volume or original anisotropic source is assumed. -/
public noncomputable section
open Set MeasureTheory Function
open scoped NNReal ENNReal Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared

/-- Product submersion domination and the actual independent cube law imply
that every original unweighted noise row annihilates an original boundary
whose product with the full auxiliary state has zero reference volume. -/
theorem original_row_null_of_product
    {EP X Y ι κ : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [MetricSpace X] [MetricSpace Y] [ChartedSpace EP (X × Y)]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace (X × Y)]
    [Fintype ι] [Fintype κ]
    {TP : (X × Y) ≃ₜ (X × Y)} {r : ℝ}
    (P : Maps (E := EP) (ι := ι ⊕ κ) TP r)
    (L : Laws (ι := ι)) (L' : Laws (ι := κ))
    (σ : Measure (X × Y))
    (source : ControlSubmersionSources (E := EP) (ι := ι ⊕ κ) σ)
    (ε : ℝ≥0) (hε : 0 < ε) (window : ε ≤ P.window)
    (F : X × cube (ι := ι) ε → X) (G : Y × cube (ι := κ) ε → Y)
    (hF : Measurable F) (hG : Measurable G)
    (independent : ∀ (a : cube (ι := ι ⊕ κ) ε) (z : X × Y),
      P.family ε a.val z =
        (F (z.1, (NoiseCubeRescaling.splitCube (ε : ℝ) a).1),
         G (z.2, (NoiseCubeRescaling.splitCube (ε : ℝ) a).2)))
    (B : Set X) (_hB : MeasurableSet B) (null : σ (B ×ˢ (univ : Set Y)) = 0)
    (y : Y) (x : X) :
    ((L.law ε).map (fun a => F (x, a))) B = 0 := by
  let : IsProbabilityMeasure (L.law ε) := L.probability ε
  let : IsProbabilityMeasure (L'.law ε) := L'.probability ε
  let : IsProbabilityMeasure ((productLaws L L').law ε) := (productLaws L L').probability ε
  let joint := fun a : cube (ι := ι ⊕ κ) ε => P.family ε a.val (x, y)
  have hj : Measurable joint :=
    (P.raw_measurable ε hε window).comp measurable_prodMk_left
  obtain ⟨C, _hC, bound⟩ := P.volume_bound_from_submersion σ source ε hε window
  have ac : (((productLaws L L').law ε).map joint) ≪ σ := by
    obtain ⟨q, _hq, D, _hD, _hqD, law⟩ := (productLaws L L').bounded_density ε hε
    rw [law]
    exact ((withDensity_absolutelyContinuous (cubeVolume (ι := ι ⊕ κ) ε) q).map hj).trans
      (Measure.absolutelyContinuous_of_le_smul (bound (x, y)))
  have hf : Measurable (fun a => F (x, a)) := hF.comp measurable_prodMk_left
  have hg : Measurable (fun a => G (y, a)) := hG.comp measurable_prodMk_left
  have factor : (((productLaws L L').law ε).map joint) =
      ((L.law ε).map (fun a => F (x, a))).prod
        ((L'.law ε).map (fun a => G (y, a))) := by
    rw [Measure.map_prod_map _ _ hf hg, ← productLaws_split L L' ε,
      Measure.map_map (hf.prodMap hg) (NoiseCubeRescaling.splitCube (ε : ℝ)).measurable]
    congr 1
    funext a
    exact independent a (x, y)
  have hz := ac null
  rw [factor, Measure.prod_prod, Measure.map_apply hg MeasurableSet.univ] at hz
  simpa only [preimage_univ, measure_univ, mul_one] using hz

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
