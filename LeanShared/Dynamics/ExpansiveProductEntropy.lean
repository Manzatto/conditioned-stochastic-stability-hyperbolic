module

import all LeanShared.Dynamics.DynamicalEntropyProduct
public import LeanShared.Dynamics.JointProductPartitionEntropy
public import LeanShared.Dynamics.ExpansiveGeneratorEntropy
public import LeanShared.Dynamics.SmallBoundaryPartition

/-! Every invariant joining of two compact expansive systems has full
metric entropy at most the sum of the entropies of its actual marginals.
Independence and equality are not assumed. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

 theorem entropy_joining_le (T : X ≃ₜ X) (S : Y ≃ₜ Y) (c d : ℝ)
    (cpositive : 0 < c) (dpositive : 0 < d)
    (expansiveT : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (expansiveS : ∀ x y, (∀ n : ℕ,
      dist ((S : Y → Y)^[n] x) ((S : Y → Y)^[n] y) ≤ d ∧
      dist ((S.symm : Y → Y)^[n] x) ((S.symm : Y → Y)^[n] y) ≤ d) → x=y)
    (μ : ProbabilityMeasure (X × Y))
    (invariant : MeasurePreserving (T.prodCongr S) (μ : Measure (X × Y)) (μ : Measure (X × Y))) :
    entropy (T.prodCongr S) (μ : Measure (X × Y)) ≤
      entropy T ((μ : Measure (X × Y)).map Prod.fst)+entropy S ((μ : Measure (X × Y)).map Prod.snd) := by
  let TX := T.prodCongr S
  let μX := μ.map Prod.fst
  let μY := μ.map Prod.snd
  have TXeq : (TX : X × Y → X × Y) = fun z => (T z.1,S z.2) := by funext z; rfl
  have invX : MeasurePreserving T (μX : Measure X) (μX : Measure X) :=
    MeasurePreserving.of_semiconj ⟨measurable_fst,rfl⟩ invariant (fun _ => rfl) T.continuous.measurable
  have invY : MeasurePreserving S (μY : Measure Y) (μY : Measure Y) :=
    MeasurePreserving.of_semiconj ⟨measurable_snd,rfl⟩ invariant (fun _ => rfl) S.continuous.measurable
  have expansive : ∀ x y : X × Y, (∀ j : ℕ,
      dist ((TX : X × Y → X × Y)^[j] x) ((TX : X × Y → X × Y)^[j] y) ≤ min c d ∧
      dist ((TX.symm : X × Y → X × Y)^[j] x) ((TX.symm : X × Y → X × Y)^[j] y) ≤ min c d) → x=y := by
    intro x y small
    apply Prod.ext
    · apply expansiveT
      intro j
      have h := small j
      change dist ((fun z : X × Y => (T z.1,S z.2))^[j] x)
        ((fun z : X × Y => (T z.1,S z.2))^[j] y) ≤ _ ∧
        dist ((fun z : X × Y => (T.symm z.1,S.symm z.2))^[j] x)
        ((fun z : X × Y => (T.symm z.1,S.symm z.2))^[j] y) ≤ _ at h
      simp only [MeasurablePartition.iterate_product,Prod.dist_eq,max_le_iff] at h
      exact ⟨h.1.1.trans (min_le_left c d),h.2.1.trans (min_le_left c d)⟩
    · apply expansiveS
      intro j
      have h := small j
      change dist ((fun z : X × Y => (T z.1,S z.2))^[j] x)
        ((fun z : X × Y => (T z.1,S z.2))^[j] y) ≤ _ ∧
        dist ((fun z : X × Y => (T.symm z.1,S.symm z.2))^[j] x)
        ((fun z : X × Y => (T.symm z.1,S.symm z.2))^[j] y) ≤ _ at h
      simp only [MeasurablePartition.iterate_product,Prod.dist_eq,max_le_iff] at h
      exact ⟨h.1.2.trans (min_le_right c d),h.2.2.trans (min_le_right c d)⟩
  obtain ⟨k,P,_,meshP⟩ := exists_small_boundary_partition (μX : Measure X) (min c d) (lt_min cpositive dpositive)
  obtain ⟨l,Q,_,meshQ⟩ := exists_small_boundary_partition (μY : Measure Y) (min c d) (lt_min cpositive dpositive)
  have meshR (i) (x y : X × Y) (hx : x ∈ (P.product Q).atom i) (hy : y ∈ (P.product Q).atom i) :
      dist x y ≤ min c d := by
    change x.1 ∈ P.atom _ ∧ x.2 ∈ Q.atom _ at hx
    change y.1 ∈ P.atom _ ∧ y.2 ∈ Q.atom _ at hy
    exact max_le (meshP _ _ _ hx.1 hy.1).le (meshQ _ _ _ hx.2 hy.2).le
  have rates : (P.product Q).entropyRate TX (μ : Measure (X × Y)) ≤
      P.entropyRate T (μX : Measure X)+Q.entropyRate S (μY : Measure Y) := by
    apply le_of_tendsto_of_tendsto ((P.product Q).entropyRate_tendsto TX (μ : Measure (X × Y)) invariant)
      ((P.entropyRate_tendsto T (μX : Measure X) invX).add (Q.entropyRate_tendsto S (μY : Measure Y) invY))
    apply Eventually.of_forall
    intro n
    have h := div_le_div_of_nonneg_right
      (P.dynamicalEntropy_joint_product_le Q T S T.continuous.measurable S.continuous.measurable (μ : Measure (X × Y)) n)
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rw [←TXeq] at h
    simpa only [add_div,μX,μY,ProbabilityMeasure.toMeasure_map] using h
  rw [←(ProbabilityMeasure.toMeasure_map μ (f := Prod.fst)),
    ←(ProbabilityMeasure.toMeasure_map μ (f := Prod.snd))]
  rw [(P.product Q).entropy_eq_generator_rate TX (min c d) expansive meshR μ invariant,
    P.entropy_eq_generator_rate T c expansiveT (fun i x y hx hy => (meshP i x y hx hy).le.trans (min_le_left c d)) μX invX,
    Q.entropy_eq_generator_rate S d expansiveS (fun i x y hx hy => (meshQ i x y hx hy).le.trans (min_le_right c d)) μY invY,
    ←EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr rates

end LeanShared.ThermodynamicDefinitions
