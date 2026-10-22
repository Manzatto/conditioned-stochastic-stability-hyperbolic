module

public import LeanShared.Analysis.ChartWordControlSystem

/-! Shrinking ordinary local calculus domains preserves the literal actual
controls predicate. Derived distortion neighborhoods can therefore be added
without changing the classical microscopic parameters or kernel theorem. -/

@[expose] public noncomputable section
open Set
namespace LeanShared.ChartWordControlSystem.Data
variable {E M Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [TopologicalSpace Ω]
  {F : Ω → M ≃ₜ M} {reference : Ω} {N : ℕ} (d : ChartWordControlSystem.Data (E := E) F reference N)

def narrow (W : Set Ω) (hW : IsOpen W) (href : reference ∈ W) :
    ChartWordControlSystem.Data (E := E) F reference N :=
  { d with
    U := d.U ∩ W
    U_open := d.U_open.inter hW
    reference_mem := ⟨d.reference_mem, href⟩
    composition := fun word hw => d.composition word (fun i => (hw i).1) }

theorem narrow_predicate (W : Set Ω) (hW : IsOpen W) (href : reference ∈ W)
    (p : MicrolocalBlockParameters.Parameters) (word : Fin N → Ω) :
    (d.narrow W hW href).predicate p word ↔ d.predicate p word := Iff.rfl

end LeanShared.ChartWordControlSystem.Data
