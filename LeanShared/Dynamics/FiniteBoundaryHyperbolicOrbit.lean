module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicTransform

/-! The finite Lyapunov--Perron fixed point constructs the actual orbit
segment with independent initial stable/final unstable boundary values.
No finite orbit, shooting solution or volume conclusion is assumed. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform
open scoped NNReal
namespace Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace U] [CompleteSpace S] {N : ℕ}

@[expose] def orbit (d : Data U S N) (boundary : U × S) : Fin (N + 1) → U × S :=
  (d.transform_contracting boundary).fixedPoint (d.raw boundary)

theorem orbit_raw (d : Data U S N) (boundary : U × S) (j : Fin (N + 1)) :
    d.raw boundary (d.orbit boundary) j = d.orbit boundary j :=
  congrFun (d.transform_contracting boundary).fixedPoint_isFixedPt j

theorem orbit_initial_stable (d : Data U S N) (boundary : U × S) :
    (d.orbit boundary ⟨0, by omega⟩).2 = boundary.2 := by
  have stable := congrArg Prod.snd (d.orbit_raw boundary ⟨0, by omega⟩)
  simpa only [raw, Nat.lt_irrefl, dite_eq_right, not_false_eq_true] using stable.symm

theorem orbit_final_unstable (d : Data U S N) (boundary : U × S) :
    (d.orbit boundary ⟨N, by omega⟩).1 = boundary.1 := by
  have unstable := congrArg Prod.fst (d.orbit_raw boundary ⟨N, by omega⟩)
  simpa only [raw, Nat.lt_irrefl, dite_eq_right, not_false_eq_true] using unstable.symm

@[expose] def map (d : Data U S N) (i : Fin N) (z : U × S) : U × S :=
  (d.expanding i z.1 + (d.nonlinear i z).1,
    d.contracting i z.2 + (d.nonlinear i z).2)

theorem orbit_step (d : Data U S N) (boundary : U × S) (i : Fin N) :
    d.map i (d.orbit boundary ⟨i.val, by omega⟩) = d.orbit boundary ⟨i.val + 1, by omega⟩ := by
  have unstable := congrArg Prod.fst (d.orbit_raw boundary ⟨i.val, by omega⟩)
  have stable := congrArg Prod.snd (d.orbit_raw boundary ⟨i.val + 1, by omega⟩)
  have before : i.val < N := i.isLt
  have after : 0 < i.val + 1 := by omega
  simp only [raw, dite_eq_left before, Fin.eta] at unstable
  simp only [raw, dite_eq_left after, Nat.add_sub_cancel, Fin.eta] at stable
  apply Prod.ext
  · have expanded := congrArg (d.expanding i) unstable
    rw [(d.expanding i).apply_symm_apply] at expanded
    exact eq_sub_iff_add_eq.mp expanded.symm
  · exact stable

end Data
end LeanShared.FiniteBoundaryHyperbolicTransform
