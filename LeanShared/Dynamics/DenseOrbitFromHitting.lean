module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Dynamics.FixedPoints.Basic

/-! Birkhoff's dense-orbit argument in the exact open-set hitting form.
Only countable basis, Baire, continuity and nonemptiness are used. -/

public noncomputable section
open Set Topology
namespace LeanShared

 theorem exists_dense_forward_orbit {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [BaireSpace X] [Nonempty X]
    (f : X → X) (continuous : Continuous f)
    (hitting : ∀ U V : Set X, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
      ∃ n : ℕ, ∃ x ∈ U, f^[n] x ∈ V) :
    ∃ x : X, Dense (range (fun n : ℕ => f^[n] x)) := by
  let basis := TopologicalSpace.countableBasis X
  have countable : basis.Countable := TopologicalSpace.countable_countableBasis X
  have basic : TopologicalSpace.IsTopologicalBasis basis := TopologicalSpace.isBasis_countableBasis X
  let visits (U : Set X) : Set X := ⋃ n : ℕ, f^[n] ⁻¹' U
  have open_visits (U : Set X) (hU : U ∈ basis) : IsOpen (visits U) :=
    isOpen_iUnion (fun n => (basic.isOpen hU).preimage (continuous.iterate n))
  have dense_visits (U : Set X) (hU : U ∈ basis) : Dense (visits U) := by
    apply dense_iff_inter_open.mpr
    intro V openV nonemptyV
    have nonemptyU : U.Nonempty := Set.nonempty_iff_ne_empty.mpr (by
      intro equal
      have forbidden := TopologicalSpace.empty_notMem_countableBasis X
      exact forbidden (equal ▸ hU))
    obtain ⟨n, x, inV, enters⟩ := hitting V U openV (basic.isOpen hU) nonemptyV nonemptyU
    exact ⟨x, inV, mem_iUnion.mpr ⟨n, enters⟩⟩
  have dense_all : Dense (⋂ U ∈ basis, visits U) :=
    dense_biInter_of_isOpen open_visits countable dense_visits
  obtain ⟨x, hx⟩ := dense_all.nonempty
  refine ⟨x, basic.dense_iff.mpr ?_⟩
  intro U hU _nonempty
  have visit := mem_iInter.mp (mem_iInter.mp hx U) hU
  obtain ⟨n, hn⟩ := mem_iUnion.mp visit
  exact ⟨f^[n] x, hn, mem_range_self n⟩

end LeanShared
