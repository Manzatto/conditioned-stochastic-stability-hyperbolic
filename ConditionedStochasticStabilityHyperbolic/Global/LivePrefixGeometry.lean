module

public import ConditionedStochasticStabilityHyperbolic.Global.ProductAdaptedFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.NestedLayerKernel

/-! Literal live prefixes are differences of compact prefixes and the open
absorbing region. Their nested subtype, direct subtype and stabilized product
coordinates are identified by the actual inclusion maps. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.LivePrefixGeometry
open LeanShared ShiftedFiltrationGeometry NestedLayerKernel
variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]

def live (P A : Set X) : Set X := P \ A

def relativeLive (P A : Set X) : Set P := (Subtype.val ⁻¹' A)ᶜ

omit [MetricSpace X] in
 theorem relativeLive_eq_innerLevel (P A : Set X) :
    relativeLive P A = innerLevel (live P A) P := by
  ext x
  simp only [relativeLive, innerLevel, live, mem_compl_iff, mem_preimage, mem_sdiff]
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

/-- Flatten the two actual memberships without any topological extension. -/
def flatten (P A : Set X) : relativeLive P A ≃ₜ live P A where
  toFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem flatten_val (P A : Set X) (x : relativeLive P A) :
    (flatten P A x).val = x.val.val := rfl

 theorem live_isCompact (P A : Set X) (hP : IsCompact P) (hA : IsOpen A) :
    IsCompact (live P A) := hP.inter_right hA.isClosed_compl

omit [MetricSpace X] [MetricSpace Y] in
 theorem live_product (P A : Set X) :
    live (P ×ˢ (univ : Set Y)) (A ×ˢ univ) = live P A ×ˢ univ := by
  ext z
  simp only [live, mem_sdiff, mem_prod, mem_univ, and_true]

variable [CompactSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y)
  (A : Set X) (Λ : I → Set X) (ℓ : ℕ) (D : AdaptedSource T A Λ ℓ)

 theorem actualLivePrefix_product [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (k : Fin ℓ) (N : ℕ) :
    live (DerivedHG2Application.actualPrefix (T.prodCongr S) (A ×ˢ univ)
      (fun j => Λ j ×ˢ univ) ℓ (ProductAdaptedFiltration.source T S A Λ ℓ D) k N)
      (A ×ˢ univ) =
      live (DerivedHG2Application.actualPrefix T A Λ ℓ D k N) A ×ˢ univ := by
  rw [ProductAdaptedFiltration.actualPrefix_product, live_product]

end ConditionedStochasticStabilityHyperbolic.Global.LivePrefixGeometry
