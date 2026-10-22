module

public import LeanShared.Analysis.ChartWordControlSystem

/-! Literal finite arrays of actual chart-word controls provide the
pressure-source parameterControl and validNeighborhood fields. All tuple
neighborhoods are constructed from the ordinary pre-control data. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.ChartWordControlFamily
variable {E M Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [TopologicalSpace Ω]
  {F : Ω → M ≃ₜ M} {reference : Ω} {J : ℕ → Type*} [∀ N, Finite (J N)]
  (d : ∀ N, J N → ChartWordControlSystem.Data (E := E) F reference N)

abbrev Parameters (J : ℕ → Type*) := ∀ N, J N → MicrolocalBlockParameters.Parameters

def predicate (N : ℕ) (p : Parameters J) (word : Fin N → Ω) : Prop :=
  ∀ j, (d N j).predicate (p N j) word

/-- Actual open generator cone/calculus domains at the selected finite word. -/
def valid (N : ℕ) : Set (Fin N → Ω) :=
  {word | ∀ j i, word i ∈ (d N j).U}

theorem valid_open (N : ℕ) : IsOpen (valid d N) := by
  have heq : valid d N = ⋂ j : J N, ⋂ i : Fin N, (fun word : Fin N → Ω => word i) ⁻¹' (d N j).U := by
    ext word
    simp only [valid, mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [heq]
  exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun i =>
    (d N j).U_open.preimage (continuous_apply i)

theorem valid_neighborhood (N : ℕ) : valid d N ∈ 𝓝 (fun _ => reference) :=
  (valid_open d N).mem_nhds (fun j _ => (d N j).reference_mem)

/-- One global array type works at every word length; only the selected
finite slice is used by each actual local kernel estimate. -/
theorem parameter_control : ∀ N, ∃ p : Parameters J, ∃ V : Set (Fin N → Ω),
    V ∈ 𝓝 (fun _ => reference) ∧ ∀ word ∈ V, predicate d N p word := by
  classical
  have hlocal := fun N j => (d N j).exists_controls
  choose p U hU href hsub hcontrols using hlocal
  intro N
  let V : Set (Fin N → Ω) := ⋂ j : J N, ⋂ i : Fin N, (fun word => word i) ⁻¹' U N j
  have hV : IsOpen V := isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun i =>
    (hU N j).preimage (continuous_apply i)
  refine ⟨p, V, hV.mem_nhds (mem_iInter.mpr fun j => mem_iInter.mpr fun _ => href N j), ?_⟩
  intro word hw j
  exact hcontrols N j word (fun i => mem_iInter.mp (mem_iInter.mp hw j) i)

end LeanShared.ChartWordControlFamily
