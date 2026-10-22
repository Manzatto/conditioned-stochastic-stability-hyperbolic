module

public import LeanShared.Analysis.DyadicCompletion

/-! # Explicit transport along a proved physical core-map identity

An opaque core identity transports a completed realization with its norm and
core law preserved. This avoids repeatedly normalizing nested Lp instances
when physical chart constructions have different definitional presentations.
-/

@[expose] public noncomputable section
namespace LeanShared.CompletedRealizationTransport
open DyadicCompletion
variable {Core B R : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup R] [NormedSpace ℂ R]
  (q r : Core →ₗ[ℂ] B) (h : q = r)

def transport (A : R →L[ℂ] closedCore q) : R →L[ℂ] closedCore r := h ▸ A

theorem norm_transport (A : R →L[ℂ] closedCore q) (f : R) :
    ‖transport q r h A f‖ = ‖A f‖ := by
  subst r
  rfl

theorem transport_core (A : R →L[ℂ] closedCore q) (cR : Core →ₗ[ℂ] R)
    (core : ∀ c, A (cR c) = coreLift q c) (c : Core) :
    transport q r h A (cR c) = coreLift r c := by
  subst r
  exact core c

end LeanShared.CompletedRealizationTransport
