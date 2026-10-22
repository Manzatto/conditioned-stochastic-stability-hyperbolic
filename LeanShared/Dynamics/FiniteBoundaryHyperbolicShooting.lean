module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicParameter

/-! Actual finite two-boundary shooting is a constructed homeomorphism.
Its inverse is the literal finite nonlinear evolution followed by final
unstable/initial stable observation; no shooting map is assumed. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform
namespace Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] {N : ℕ}

@[expose] def evolve (d : Data U S N) (z : U × S) : ℕ → U × S
  | 0 => z
  | n + 1 => if h : n < N then d.map ⟨n, h⟩ (d.evolve z n) else d.evolve z n

theorem evolve_step (d : Data U S N) (z : U × S) (i : Fin N) :
    d.evolve z (i.val + 1) = d.map i (d.evolve z i.val) := by
  simp only [evolve, dite_eq_left i.isLt, Fin.eta]

theorem map_continuous (d : Data U S N) (i : Fin N) : Continuous (d.map i) :=
  (((d.expanding i).continuous.comp continuous_fst).add (d.nonlinear_bound i).continuous.fst).prodMk
    (((d.contracting i).continuous.comp continuous_snd).add (d.nonlinear_bound i).continuous.snd)

theorem evolve_continuous (d : Data U S N) (n : ℕ) : Continuous (fun z => d.evolve z n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    by_cases before : n < N
    · simpa only [evolve, dite_eq_left before, Function.comp_def] using (d.map_continuous ⟨n, before⟩).comp ih
    · simpa only [evolve, dite_eq_right before] using ih

@[expose] def shooting (d : Data U S N) (z : U × S) : U × S := ((d.evolve z N).1, z.2)

theorem shooting_continuous (d : Data U S N) : Continuous d.shooting :=
  (d.evolve_continuous N).fst.prodMk continuous_snd

variable [CompleteSpace U] [CompleteSpace S]

theorem evolve_orbit (d : Data U S N) (boundary : U × S) (j : ℕ) (hj : j ≤ N) :
    d.evolve (d.orbit boundary ⟨0, Nat.zero_lt_succ N⟩) j = d.orbit boundary ⟨j, by omega⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have before : j < N := by omega
    rw [d.evolve_step _ ⟨j, before⟩, ih (by omega)]
    exact d.orbit_step boundary ⟨j, before⟩

theorem shooting_initial (d : Data U S N) (boundary : U × S) :
    d.shooting (d.orbit boundary ⟨0, Nat.zero_lt_succ N⟩) = boundary := by
  apply Prod.ext
  · change (d.evolve (d.orbit boundary ⟨0, Nat.zero_lt_succ N⟩) N).1 = _
    rw [d.evolve_orbit boundary N le_rfl]
    exact d.orbit_final_unstable boundary
  · exact d.orbit_initial_stable boundary

theorem initial_shooting (d : Data U S N) (z : U × S) :
    d.orbit (d.shooting z) ⟨0, Nat.zero_lt_succ N⟩ = z := by
  let path : Fin (N + 1) → U × S := fun j => d.evolve z j.val
  have same : path = d.orbit (d.shooting z) := by
    apply d.orbit_unique (d.shooting z) path rfl rfl
    intro i
    exact (d.evolve_step z i).symm
  exact (congrFun same ⟨0, Nat.zero_lt_succ N⟩).symm

@[expose] def shootingHomeomorph (d : Data U S N) : (U × S) ≃ₜ (U × S) where
  toFun := fun boundary => d.orbit boundary ⟨0, Nat.zero_lt_succ N⟩
  invFun := d.shooting
  left_inv := d.shooting_initial
  right_inv := d.initial_shooting
  continuous_toFun := by
    simpa only [Function.comp_def] using
      (continuous_apply (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1))).comp d.orbit_continuous
  continuous_invFun := d.shooting_continuous

end Data
end LeanShared.FiniteBoundaryHyperbolicTransform
