module

public import LeanShared.Dynamics.HyperbolicBasicSet

/-! Cartesian products preserve the literal two-sided isolated core and
open-set mixing. These statements use the actual homeomorphisms, rather
than independently supplied symbolic dynamics. -/

@[expose] public noncomputable section
open Set Function
namespace LeanShared

variable {X Y : Type*}

theorem iterate_independent (f : X → X) (g : Y → Y) (n : ℕ) (z : X × Y) :
    (Prod.map f g)^[n] z = (f^[n] z.1, g^[n] z.2) := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [Function.iterate_succ_apply', hn, Prod.map_apply]

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem isolatedCore_product (T : X ≃ₜ X) (S : Y ≃ₜ Y) (K : Set X) (L : Set Y) :
    isolatedCore (T.prodCongr S) (K ×ˢ L) = isolatedCore T K ×ˢ isolatedCore S L := by
  ext z
  change ((∀ n, (Prod.map T S)^[n] z ∈ K ×ˢ L) ∧
    ∀ n, (Prod.map T.symm S.symm)^[n] z ∈ K ×ˢ L) ↔
    ((∀ n, (T : X → X)^[n] z.1 ∈ K) ∧ ∀ n, (T.symm : X → X)^[n] z.1 ∈ K) ∧
      ((∀ n, (S : Y → Y)^[n] z.2 ∈ L) ∧ ∀ n, (S.symm : Y → Y)^[n] z.2 ∈ L)
  simp only [iterate_independent, mem_prod, forall_and]
  tauto

end LeanShared

namespace LeanShared.HyperbolicBasicSet

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Product mixing follows from the same eventual time for both factors. -/
theorem MixingOn.product {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
    (hT : MixingOn T K) (hS : MixingOn S L) : MixingOn (T.prodCongr S) (K ×ˢ L) := by
  intro U W hU hW hKU hKW
  obtain ⟨⟨x, y⟩, ⟨⟨hxK, hyL⟩, hxyU⟩⟩ := hKU
  obtain ⟨⟨a, b⟩, ⟨⟨haK, hbL⟩, habW⟩⟩ := hKW
  obtain ⟨UX, UY, hUX, hUY, hxU, hyU, hprodU⟩ := isOpen_prod_iff.mp hU x y hxyU
  obtain ⟨WX, WY, hWX, hWY, haW, hbW, hprodW⟩ := isOpen_prod_iff.mp hW a b habW
  obtain ⟨NX, hNX⟩ := hT UX WX hUX hWX ⟨x, hxK, hxU⟩ ⟨a, haK, haW⟩
  obtain ⟨NY, hNY⟩ := hS UY WY hUY hWY ⟨y, hyL, hyU⟩ ⟨b, hbL, hbW⟩
  refine ⟨max NX NY, ?_⟩
  intro n hn
  obtain ⟨v, hv, hvW⟩ := hNX n ((le_max_left _ _).trans hn)
  obtain ⟨w, hw, hwW⟩ := hNY n ((le_max_right _ _).trans hn)
  refine ⟨(v, w), ⟨⟨hv.1, hw.1⟩, hprodU ⟨hv.2, hw.2⟩⟩, ?_⟩
  change (Prod.map T S)^[n] (v, w) ∈ W
  rw [iterate_independent]
  exact hprodW ⟨hvW, hwW⟩

end LeanShared.HyperbolicBasicSet
