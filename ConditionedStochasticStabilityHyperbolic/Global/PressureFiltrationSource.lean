module

public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedBoundaryGeometry
public import LeanShared.Dynamics.PressureTopologicalOrder

/-!
# Classical adapted filtration for the checked pressure-compatible order

The graph/pressure algorithm constructs the enumeration. The only deferred
classical source is existence of a smooth adapted filtration for a given
compatible finite enumeration, as invoked in the manuscript's Shub/Conley
filtration argument. Its positive levels are smooth; absorbing A stays an
unrestricted open zero level. No QEM, compact analytic embedding, spectral
estimate, or conditioned limit appears in this source contract.
-/

@[expose] public noncomputable section
open Set Relation
namespace ConditionedStochasticStabilityHyperbolic.Global.PressureFiltrationSource
open LeanShared PressureTopologicalOrder ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X]

/-- The source-first graph enumeration is reversed for increasing filtration
levels, so a heteroclinic target occupies a lower level than its source. -/
def reversedVertex (L : List I) (i : Fin L.length) : I :=
  L.get ⟨L.length - 1 - i.val, by omega⟩

/-- Precise deferred classical smooth-filtration theorem. `SmoothLevel` is
an actual codimension-zero submanifold-with-boundary predicate supplied by
manifold geometry; its volume-null boundary consequence is separate. -/
def ClassicalCompatibleFiltrationContract
    (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (edge : I → I → Prop)
    (R : Finset I) (SmoothLevel : Set X → Prop) : Prop :=
  R.Nonempty → ∀ L : List I,
    (∀ v, v ∈ L ↔ v ∈ R) → L.Nodup →
    (∀ i j : Fin L.length, edge (L.get i) (L.get j) → i < j) →
    ∃ D : AdaptedSource T A Λ L.length,
      D.index = reversedVertex L ∧
      ∀ i, 0 < i → i ≤ L.length → SmoothLevel (D.levels i)

/-- No cycles plus the checked pressure algorithm and cited adapted
filtration existence give an actual smooth source in the correct order. -/
theorem exists_pressure_compatible_smooth_source [Finite I]
    (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (edge : I → I → Prop)
    (pressure : I → ℝ) (hacyclic : ∀ v, ¬TransGen edge v v)
    (R : Finset I) (hR : R.Nonempty) (SmoothLevel : Set X → Prop)
    (hclassical : ClassicalCompatibleFiltrationContract T A Λ edge R SmoothLevel) :
    ∃ L : List I, (∀ v, v ∈ L ↔ v ∈ R) ∧ L.Nodup ∧
      (∀ i j : Fin L.length, edge (L.get i) (L.get j) → i < j) ∧
      ∃ D : AdaptedSource T A Λ L.length,
        D.index = reversedVertex L ∧
        ∀ i, 0 < i → i ≤ L.length → SmoothLevel (D.levels i) := by
  classical
  let L := blockOrder edge pressure (wellFounded_of_acyclic edge hacyclic)
    (PressureBlocks.blocks edge pressure R)
  obtain ⟨hcover, hnodup, hedge⟩ := acyclic_pressureBlocks_order_spec edge pressure hacyclic R
  obtain ⟨D, hindex, hsmooth⟩ := hclassical hR L hcover hnodup hedge
  exact ⟨L, hcover, hnodup, hedge, D, hindex, hsmooth⟩

section Boundary
variable [MeasurableSpace X]

/-- The classical smooth-boundary volume theorem supplies the exact
positive-boundary assumptions consumed by shifted-layer geometry. -/
theorem positive_boundary_null_of_smooth_source
    (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
    (D : AdaptedSource T A Λ ℓ) (σ : MeasureTheory.Measure X)
    (SmoothLevel : Set X → Prop)
    (hsmooth : ∀ i, 0 < i → i ≤ ℓ → SmoothLevel (D.levels i))
    (hclassicalNull : ∀ K : Set X, SmoothLevel K → σ (frontier K) = 0) :
    ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0 := by
  intro i hi hiℓ
  exact hclassicalNull _ (hsmooth i hi hiℓ)

end Boundary
end ConditionedStochasticStabilityHyperbolic.Global.PressureFiltrationSource
