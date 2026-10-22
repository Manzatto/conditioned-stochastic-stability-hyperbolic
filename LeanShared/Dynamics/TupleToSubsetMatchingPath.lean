module

public import LeanShared.Dynamics.SignedSubsetMatchingGraph

/-! Quotient an actual separated ordered tuple path to the finite signed
matching-edge graph.  Canonical subset enumerations retain the precise
matching bijection rather than collapsing multiple possible edges.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [DecidableEq A] {R E : A → A → Prop} {k : ℕ}

@[expose] def tupleVertex (u : Fin k → A) (injective : Injective u)
    (related : ∀ i j, E (u i) (u j)) : FiberSubset E k := by
  refine ⟨Finset.univ.image u, ?_, ?_⟩
  · simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_image_of_injective Finset.univ injective
  · intro x hx y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact related i j

@[expose] def tupleLabelEquiv (u : Fin k → A) (injective : Injective u)
    (related : ∀ i j, E (u i) (u j)) : Fin k ≃ (tupleVertex u injective related).val := by
  let f : Fin k → (tupleVertex u injective related).val :=
    fun i => ⟨u i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j equal
    exact injective (congrArg Subtype.val equal)
  · intro y
    obtain ⟨i, _, equal⟩ := Finset.mem_image.mp y.property
    exact ⟨i, Subtype.ext equal⟩

@[expose] def tupleOrdering (u : Fin k → A) (injective : Injective u)
    (related : ∀ i j, E (u i) (u j)) : Equiv.Perm (Fin k) :=
  (subsetEnumeration (tupleVertex u injective related)).trans (tupleLabelEquiv u injective related).symm

theorem tupleOrdering_symbol (u : Fin k → A) (injective : Injective u)
    (related : ∀ i j, E (u i) (u j)) (i : Fin k) :
    subsetSymbol (tupleVertex u injective related) i = u (tupleOrdering u injective related i) := by
  have equal := (tupleLabelEquiv u injective related).apply_symm_apply
    (subsetEnumeration (tupleVertex u injective related) i)
  exact (congrArg (fun x : (tupleVertex u injective related).val => x.val) equal).symm

@[expose] def tupleMatchingEdge (u v : Fin k → A) (hu : Injective u) (hv : Injective v)
    (eu : ∀ i j, E (u i) (u j)) (ev : ∀ i j, E (v i) (v j))
    (allowed : ∀ i, R (u i) (v i)) : SubsetMatchingEdge R E k := by
  let ou := tupleOrdering u hu eu
  let ov := tupleOrdering v hv ev
  refine ⟨(tupleVertex u hu eu, tupleVertex v hv ev, ov.trans ou.symm), ?_⟩
  intro i
  rw [tupleOrdering_symbol, tupleOrdering_symbol]
  change R (u (ou (ou.symm (ov i)))) (v (ov i))
  simpa only [Equiv.apply_symm_apply] using allowed (ov i)

@[expose] def tupleToMatchingPath (a : Path (FiberTupleTransition R E k)) :
    Path (SubsetMatchingEdgeTransition R E k) :=
  ⟨fun n => tupleMatchingEdge (a.val n) (a.val (n + 1))
      (a.property n).2.2.2.1 (a.property n).2.2.2.2
      (a.property n).2.1 (a.property n).2.2.1 (a.property n).1,
    fun _n => rfl⟩

end LeanShared.BilateralShadowingCoding
