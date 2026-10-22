module

public import LeanShared.Dynamics.ExpansiveProductEquilibrium
public import LeanShared.Dynamics.EquilibriumCoreRestriction
public import LeanShared.Dynamics.EquilibriumIsometricEmbedding
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The actual independent product of ambient equilibrium probabilities
on compact invariant expansive cores is an ambient product equilibrium.
Potential continuity is required only on each core; no product variational
principle or product equilibrium source is supplied. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions

private theorem invariant_mem {Z : Type*} [TopologicalSpace Z]
    (T : Z ≃ₜ Z) (K : Set Z) (invariant : T '' K=K) (x : Z) : x ∈ K ↔ T x ∈ K := by
  constructor
  · intro hx
    rw [←invariant]
    exact ⟨x,hx,rfl⟩
  · intro hx
    rw [←invariant] at hx
    obtain ⟨y,hy,equal⟩ := hx
    exact (T.injective equal) ▸ hy

private theorem restriction_expansive {Z : Type*} [MetricSpace Z]
    (T : Z ≃ₜ Z) (K : Set Z) (TK : K ≃ₜ K)
    (same : ∀ x, (TK x).val=T x.val) (back : ∀ x, (TK.symm x).val=T.symm x.val)
    (c : ℝ) (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : Z → Z)^[j] x) ((T : Z → Z)^[j] y) ≤ c ∧
      dist ((T.symm : Z → Z)^[j] x) ((T.symm : Z → Z)^[j] y) ≤ c) → x=y) :
    ∀ x y : K, (∀ j : ℕ,
      dist ((TK : K → K)^[j] x) ((TK : K → K)^[j] y) ≤ c ∧
      dist ((TK.symm : K → K)^[j] x) ((TK.symm : K → K)^[j] y) ≤ c) → x=y := by
  intro x y small
  apply Subtype.ext
  apply expansive x.val x.property y.val y.property
  intro j
  have h := small j
  change dist (((TK : K → K)^[j] x).val) (((TK : K → K)^[j] y).val) ≤ c ∧
    dist (((TK.symm : K → K)^[j] x).val) (((TK.symm : K → K)^[j] y).val) ≤ c at h
  simpa only [iterate_coe_restriction TK same,iterate_coe_restriction TK.symm back] using h

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] [BorelSpace (X × Y)]

theorem IsEquilibriumState.product_on_compact_cores
    (T : X ≃ₜ X) (S : Y ≃ₜ Y) (K : Set X) (J : Set Y)
    (compactK : IsCompact K) (compactJ : IsCompact J)
    (invariantK : T '' K=K) (invariantJ : S '' J=J)
    (c d : ℝ) (cpositive : 0 < c) (dpositive : 0 < d)
    (expansiveT : ∀ x ∈ K, ∀ y ∈ K, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (expansiveS : ∀ x ∈ J, ∀ y ∈ J, (∀ n : ℕ,
      dist ((S : Y → Y)^[n] x) ((S : Y → Y)^[n] y) ≤ d ∧
      dist ((S.symm : Y → Y)^[n] x) ((S.symm : Y → Y)^[n] y) ≤ d) → x=y)
    (φ : X → ℝ) (ψ : Y → ℝ) (continuousφ : ContinuousOn φ K) (continuousψ : ContinuousOn ψ J)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (stateμ : IsEquilibriumState T φ K μ) (stateν : IsEquilibriumState S ψ J ν) :
    IsEquilibriumState (T.prodCongr S) (fun z : X × Y => φ z.1+ψ z.2) (K ×ˢ J)
      (⟨(μ : Measure X).prod (ν : Measure Y),inferInstance⟩ : ProbabilityMeasure (X × Y)) := by
  let TK := T.subtype (invariant_mem T K invariantK)
  let SJ := S.subtype (invariant_mem S J invariantJ)
  have sameK (x : K) : (TK x).val=T x.val := rfl
  have sameJ (x : J) : (SJ x).val=S x.val := rfl
  obtain ⟨μK,pushK,equilibriumK⟩ := stateμ.exists_core_restriction T K compactK.isClosed.measurableSet
    TK TK.continuous.measurable sameK φ μ
  obtain ⟨νJ,pushJ,equilibriumJ⟩ := stateν.exists_core_restriction S J compactJ.isClosed.measurableSet
    SJ SJ.continuous.measurable sameJ ψ ν
  let : CompactSpace K := isCompact_iff_compactSpace.mp compactK
  let : CompactSpace J := isCompact_iff_compactSpace.mp compactJ
  have exK := restriction_expansive T K TK sameK (fun _ => rfl) c expansiveT
  have exJ := restriction_expansive S J SJ sameJ (fun _ => rfl) d expansiveS
  let fK : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨(fun x => φ x.val),continuousφ.domRestrict⟩
  let fJ : J →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨(fun x => ψ x.val),continuousψ.domRestrict⟩
  have equilibrium := IsEquilibriumState.product_of_expansive TK SJ c d cpositive dpositive
    exK exJ fK fJ μK νJ equilibriumK equilibriumJ
  let ρ : ProbabilityMeasure (K × J) := ⟨(μK : Measure K).prod (νJ : Measure J),inferInstance⟩
  let f : K × J → X × Y := Prod.map Subtype.val Subtype.val
  have isometry : Isometry f := by intro x y; rfl
  have embedding : MeasurableEmbedding f := (isometry.continuous.isClosedEmbedding isometry.injective).measurableEmbedding
  have same : Semiconj f (TK.prodCongr SJ) (T.prodCongr S) := fun _ => rfl
  have state := IsEquilibriumState.map_isometry f isometry embedding (TK.prodCongr SJ) (T.prodCongr S)
    (T.prodCongr S).continuous.measurable same (fun z : X × Y => φ z.1+ψ z.2) ρ equilibrium
  have image : range f=K ×ˢ J := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.1.property,x.2.property⟩
    · intro hz
      exact ⟨(⟨z.1,hz.1⟩,⟨z.2,hz.2⟩),rfl⟩
  have push : (ρ : Measure (K × J)).map f=(μ : Measure X).prod (ν : Measure Y) := by
    change ((μK : Measure K).prod (νJ : Measure J)).map (Prod.map Subtype.val Subtype.val)=_
    rw [←Measure.map_prod_map (μK : Measure K) (νJ : Measure J) measurable_subtype_coe measurable_subtype_coe,pushK,pushJ]
  have probabilityEq : ρ.map f=(⟨(μ : Measure X).prod (ν : Measure Y),inferInstance⟩ : ProbabilityMeasure (X × Y)) :=
    Subtype.ext push
  rw [image,probabilityEq] at state
  exact state

end LeanShared.ThermodynamicDefinitions
