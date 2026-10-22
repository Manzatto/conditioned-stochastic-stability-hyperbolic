module

public import LeanShared.Dynamics.OneSidedExponentialPotential
public import LeanShared.Dynamics.PressureCoboundary
public import LeanShared.Dynamics.PeriodicMatchingWeightedFiber

/-! The explicit future cohomology preserves literal periodic energies
and weights.  The one-sided restriction is an actual semiconjugacy, so
the transfer-theory potential has exactly the required periodic data.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

theorem oneSidedPotential_orbitSum (φ : Path R → ℝ) (variation : HasExponentialVariations φ)
    (n : ℕ) (a : Path R) :
    orbitSum (shift R) φ n a =
      orbitSum futureShift (oneSidedPotential φ) n (futureRestriction a) +
        resetTransfer φ a - resetTransfer φ ((shift R : _ → _)^[n] a) := by
  have energy := orbitSum_coboundary (T := (shift R : Path R → Path R)) (K := univ)
    (φ := φ) (ψ := oneSidedPotential φ ∘ futureRestriction) (u := resetTransfer φ)
    (mapsTo_univ _ _) (fun b _ => oneSidedPotential_cohomology φ variation b) n (mem_univ a)
  rw [orbitSum_of_semiconjugacy futureRestriction (shift R) futureShift
    futureRestriction_shift (oneSidedPotential φ)] at energy
  exact energy

theorem futureRestriction_periodic (n : ℕ) (a : Path R)
    (fixed : (shift R : Path R → Path R)^[n] a = a) :
    (futureShift : FuturePath R → FuturePath R)^[n] (futureRestriction a) = futureRestriction a := by
  have same : Semiconj (futureRestriction : Path R → FuturePath R) (shift R) futureShift :=
    futureRestriction_shift
  rw [← same.iterate_right n a, fixed]

theorem oneSidedPotential_periodic_energy (φ : Path R → ℝ) (variation : HasExponentialVariations φ)
    (n : ℕ) (a : Path R) (fixed : (shift R : Path R → Path R)^[n] a = a) :
    orbitSum (shift R) φ n a =
      orbitSum futureShift (oneSidedPotential φ) n (futureRestriction a) := by
  rw [oneSidedPotential_orbitSum φ variation n a, fixed]
  ring

theorem oneSidedPotential_periodic_weight (φ : Path R → ℝ) (variation : HasExponentialVariations φ)
    (n : ℕ) (a : Path R) (fixed : (shift R : Path R → Path R)^[n] a = a) :
    Real.exp (orbitSum (shift R) φ n a) =
      Real.exp (orbitSum futureShift (oneSidedPotential φ) n (futureRestriction a)) :=
  congrArg Real.exp (oneSidedPotential_periodic_energy φ variation n a fixed)

end LeanShared.BilateralShadowingCoding
