module

public import LeanShared.Dynamics.ExpansiveProductPressure
public import LeanShared.Dynamics.PressureIsometricEmbedding
public import LeanShared.Dynamics.PressureInvariantSubtype
import all LeanShared.Dynamics.CompactCoreProductEquilibrium

/-! Actual pressure is additive on arbitrary compact invariant expansive
cores. The proof transfers actual separated sets by isometries and invokes
the proved full variational product theorem on the invariant subtypes. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pressure_product_on_compact_cores
    (T : X ≃ₜ X) (S : Y ≃ₜ Y) (K : Set X) (J : Set Y)
    (compactK : IsCompact K) (compactJ : IsCompact J) (nonemptyK : K.Nonempty) (nonemptyJ : J.Nonempty)
    (invariantK : T '' K=K) (invariantJ : S '' J=J)
    (c d : ℝ) (cpositive : 0 < c) (dpositive : 0 < d)
    (expansiveT : ∀ x ∈ K, ∀ y ∈ K, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x=y)
    (expansiveS : ∀ x ∈ J, ∀ y ∈ J, (∀ n : ℕ,
      dist ((S : Y → Y)^[n] x) ((S : Y → Y)^[n] y) ≤ d ∧
      dist ((S.symm : Y → Y)^[n] x) ((S.symm : Y → Y)^[n] y) ≤ d) → x=y)
    (φ : X → ℝ) (ψ : Y → ℝ) (continuousφ : ContinuousOn φ K) (continuousψ : ContinuousOn ψ J)
 :
    pressure (T.prodCongr S) (fun z : X × Y => φ z.1+ψ z.2) (K ×ˢ J)=
      pressure T φ K+pressure S ψ J := by
  let TK := T.subtype (invariant_mem T K invariantK)
  let SJ := S.subtype (invariant_mem S J invariantJ)
  have sameK (x : K) : (TK x).val=T x.val := rfl
  have sameJ (x : J) : (SJ x).val=S x.val := rfl
  let : CompactSpace K := isCompact_iff_compactSpace.mp compactK
  let : CompactSpace J := isCompact_iff_compactSpace.mp compactJ
  let : Nonempty K := nonemptyK.to_subtype
  let : Nonempty J := nonemptyJ.to_subtype
  let : MeasurableSpace K := borel K
  let : MeasurableSpace J := borel J
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace J := ⟨rfl⟩
  have exK := restriction_expansive T K TK sameK (fun _ => rfl) c expansiveT
  have exJ := restriction_expansive S J SJ sameJ (fun _ => rfl) d expansiveS
  let fK : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨(fun x => φ x.val),continuousφ.domRestrict⟩
  let fJ : J →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨(fun x => ψ x.val),continuousψ.domRestrict⟩
  have productPressure := pressure_product_eq TK SJ c d cpositive dpositive exK exJ fK fJ
  let f : K × J → X × Y := Prod.map Subtype.val Subtype.val
  have iso : Isometry f := by intro x y; rfl
  have image : range f=K ×ˢ J := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.1.property,x.2.property⟩
    · intro hz
      exact ⟨(⟨z.1,hz.1⟩,⟨z.2,hz.2⟩),rfl⟩
  have embed := pressure_embedding f iso (TK.prodCongr SJ) (T.prodCongr S)
    (fun _ => rfl) (fun z : X × Y => φ z.1+ψ z.2)
  rw [image] at embed
  change pressure (TK.prodCongr SJ) (productPotential fK fJ) univ=_ at embed
  rw [←embed,productPressure]
  change pressure TK (fun x => φ x.val) univ+pressure SJ (fun x => ψ x.val) univ=_
  rw [pressure_restriction TK sameK φ,pressure_restriction SJ sameJ ψ]

end LeanShared.ThermodynamicDefinitions
