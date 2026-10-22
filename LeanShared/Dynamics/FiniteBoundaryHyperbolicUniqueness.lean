module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicOrbit

/-! The genuine finite two-boundary orbit is unique among all actual
segments with the same endpoints, not only among separately bounded paths. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform
namespace Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace U] [CompleteSpace S] {N : ℕ}

set_option maxHeartbeats 1200000 in
theorem orbit_unique (d : Data U S N) (boundary : U × S)
    (z : Fin (N + 1) → U × S)
    (initial : (z ⟨0, by omega⟩).2 = boundary.2)
    (final : (z ⟨N, by omega⟩).1 = boundary.1)
    (step : ∀ i : Fin N, d.map i (z ⟨i.val, by omega⟩) = z ⟨i.val + 1, by omega⟩) :
    z = d.orbit boundary := by
  apply (d.transform_contracting boundary).fixedPoint_unique
  funext j
  apply Prod.ext
  · by_cases before : j.val < N
    · change (if h : j.val < N then _ else boundary.1) = (z j).1
      rw [dite_eq_left before]
      have unstable := congrArg Prod.fst (step ⟨j.val, before⟩)
      change d.expanding ⟨j.val, before⟩ (z j).1 +
        (d.nonlinear ⟨j.val, before⟩ (z j)).1 = (z ⟨j.val + 1, by omega⟩).1 at unstable
      apply (d.expanding ⟨j.val, before⟩).injective
      rw [(d.expanding ⟨j.val, before⟩).apply_symm_apply]
      exact (eq_sub_iff_add_eq.mpr unstable).symm
    · have last : j = ⟨N, Nat.lt_succ_self N⟩ := by
        apply Fin.ext
        change j.val = N
        omega
      subst j
      simpa only [raw, Nat.lt_irrefl, dite_eq_right, not_false_eq_true] using final.symm
  · by_cases after : 0 < j.val
    · change (if h : 0 < j.val then _ else boundary.2) = (z j).2
      rw [dite_eq_left after]
      have stable := congrArg Prod.snd (step ⟨j.val - 1, by omega⟩)
      have index : j.val - 1 + 1 = j.val := by omega
      simpa only [map, index, Fin.eta] using stable
    · have first : j = ⟨0, Nat.zero_lt_succ N⟩ := by
        apply Fin.ext
        change j.val = 0
        omega
      subst j
      simpa only [raw, Nat.lt_irrefl, dite_eq_right, not_false_eq_true] using initial.symm

omit [CompleteSpace U] [CompleteSpace S] in
theorem raw_zero (d : Data U S N) : d.raw 0 (0 : Fin (N + 1) → U × S) = 0 := by
  funext j
  simp [raw, d.nonlinear_zero]

theorem orbit_zero (d : Data U S N) : d.orbit 0 = 0 :=
  ((d.transform_contracting 0).fixedPoint_unique d.raw_zero).symm

end Data
end LeanShared.FiniteBoundaryHyperbolicTransform
