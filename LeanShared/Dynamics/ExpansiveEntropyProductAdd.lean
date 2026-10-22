module

public import LeanShared.Dynamics.ExpansiveProductEntropy
public import LeanShared.Dynamics.EntropyProductLowerBound

/-! Exact full metric entropy addition for independent invariant
probabilities on compact expansive systems. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

theorem entropy_product_eq (T : X ≃ₜ X) (S : Y ≃ₜ Y) (c d : ℝ)
    (cpositive : 0 < c) (dpositive : 0 < d)
    (expansiveT : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (expansiveS : ∀ x y, (∀ n : ℕ,
      dist ((S : Y → Y)^[n] x) ((S : Y → Y)^[n] y) ≤ d ∧
      dist ((S.symm : Y → Y)^[n] x) ((S.symm : Y → Y)^[n] y) ≤ d) → x=y)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (invariantμ : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (invariantν : MeasurePreserving S (ν : Measure Y) (ν : Measure Y)) :
    entropy (T.prodCongr S) ((μ : Measure X).prod (ν : Measure Y)) =
      entropy T (μ : Measure X)+entropy S (ν : Measure Y) := by
  let ρ : ProbabilityMeasure (X × Y) := ⟨(μ : Measure X).prod (ν : Measure Y),inferInstance⟩
  have invariant : MeasurePreserving (T.prodCongr S) (ρ : Measure (X × Y)) (ρ : Measure (X × Y)) :=
    invariantμ.prod invariantν
  have upper := entropy_joining_le T S c d cpositive dpositive expansiveT expansiveS ρ invariant
  have first := (measurePreserving_fst (μ := (μ : Measure X)) (ν := (ν : Measure Y))).map_eq
  have second := (measurePreserving_snd (μ := (μ : Measure X)) (ν := (ν : Measure Y))).map_eq
  change entropy (T.prodCongr S) ((μ : Measure X).prod (ν : Measure Y)) ≤
    entropy T (((μ : Measure X).prod (ν : Measure Y)).map Prod.fst)+
    entropy S (((μ : Measure X).prod (ν : Measure Y)).map Prod.snd) at upper
  rw [first,second] at upper
  exact le_antisymm upper (entropy_product_ge T S T.continuous.measurable S.continuous.measurable (μ : Measure X) (ν : Measure Y))

end LeanShared.ThermodynamicDefinitions
