module

public import LeanShared.Analysis.MeromorphicLinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Continuous linear conjugation preserves the actual globally-defined
resolvent, including its values at spectral points, and meromorphic germs. -/

public section
namespace LeanShared.ConjugateResolvent

/-- Ring equivalences preserve the inverse extended by zero off the units. -/
theorem map_inverse {A B : Type*} [Ring A] [Ring B] (e : A ≃+* B) (a : A) :
    e (Ring.inverse a) = Ring.inverse (e a) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit]
    change e (↑u⁻¹) = Ring.inverse (↑(Units.map e.toMonoidHom u))
    rw [Ring.inverse_unit]
    rfl
  · have hb : ¬ IsUnit (e a) := by
      intro hb
      exact ha (by simpa using hb.map e.symm.toMonoidHom)
    rw [Ring.inverse_non_unit a ha, map_zero, Ring.inverse_non_unit (e a) hb]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Exact actual resolvent conjugation, valid also at spectral points. -/
theorem formula (e : E ≃L[ℂ] F) (A : E →L[ℂ] E) (z : ℂ) :
    resolvent (e.conjContinuousAlgEquiv A) z = e.arrowCongr e (resolvent A z) := by
  let φ := e.conjContinuousAlgEquiv.toAlgEquiv
  have shift : algebraMap ℂ (F →L[ℂ] F) z - φ A =
      φ (algebraMap ℂ (E →L[ℂ] E) z - A) := by rw [map_sub, φ.commutes]
  change Ring.inverse (algebraMap ℂ (F →L[ℂ] F) z - φ A) =
    φ (Ring.inverse (algebraMap ℂ (E →L[ℂ] E) z - A))
  rw [shift]
  exact (map_inverse φ.toRingEquiv _).symm

/-- Meromorphic actual resolvents are invariant under continuous conjugacy. -/
theorem meromorphicAt (e : E ≃L[ℂ] F) (A : E →L[ℂ] E) (z : ℂ)
    (h : MeromorphicAt (resolvent A) z) :
    MeromorphicAt (resolvent (e.conjContinuousAlgEquiv A)) z := by
  have mapped := MeromorphicLinearMap.map (e.arrowCongr e).toContinuousLinearMap h
  have eqfun : (fun w => e.arrowCongr e (resolvent A w)) =
      resolvent (e.conjContinuousAlgEquiv A) := funext (fun w => (formula e A w).symm)
  change MeromorphicAt (fun w => e.arrowCongr e (resolvent A w)) z at mapped
  rw [eqfun] at mapped
  exact mapped

end LeanShared.ConjugateResolvent
