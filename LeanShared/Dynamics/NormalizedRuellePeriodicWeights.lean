module

public import LeanShared.Dynamics.OneSidedNormalizedPotential
public import LeanShared.Dynamics.PressureCoboundary

/-! The actual eigenfunction normalization changes literal periodic
energies only by minus n log(eigenvalue), and periodic weights by the
exact factor eigenvalue^(-n).  No zeta identity is assumed.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

theorem normalizedPotential_orbitSum (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveH : ∀ a, 0 < h a) (n : ℕ) (a : FuturePath R) :
    orbitSum futureShift (normalizedPotential ψ h eigenvalue positiveH) n a =
      orbitSum futureShift ψ n a - (n : ℝ) * Real.log eigenvalue +
        Real.log (h a) - Real.log (h ((futureShift : FuturePath R → FuturePath R)^[n] a)) := by
  have energy := orbitSum_coboundary (T := (futureShift : FuturePath R → FuturePath R)) (K := univ)
    (φ := normalizedPotential ψ h eigenvalue positiveH)
    (ψ := fun b => ψ b - Real.log eigenvalue) (u := fun b => Real.log (h b))
    (mapsTo_univ _ _) (fun b _ => by
      change ψ b + Real.log (h b) - Real.log (h (futureShift b)) - Real.log eigenvalue = _
      ring) n (mem_univ a)
  have separated : orbitSum futureShift (fun b => ψ b - Real.log eigenvalue) n a =
      orbitSum futureShift ψ n a - (n : ℝ) * Real.log eigenvalue := by
    simp only [orbitSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [separated] at energy
  exact energy

theorem normalizedPotential_periodic_energy (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveH : ∀ a, 0 < h a) (n : ℕ) (a : FuturePath R)
    (periodic : (futureShift : FuturePath R → FuturePath R)^[n] a = a) :
    orbitSum futureShift (normalizedPotential ψ h eigenvalue positiveH) n a =
      orbitSum futureShift ψ n a - (n : ℝ) * Real.log eigenvalue := by
  rw [normalizedPotential_orbitSum, periodic]
  ring

theorem normalizedPotential_periodic_weight (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a) (n : ℕ) (a : FuturePath R)
    (periodic : (futureShift : FuturePath R → FuturePath R)^[n] a = a) :
    Real.exp (orbitSum futureShift (normalizedPotential ψ h eigenvalue positiveH) n a) =
      (eigenvalue ^ n)⁻¹ * Real.exp (orbitSum futureShift ψ n a) := by
  rw [normalizedPotential_periodic_energy ψ h eigenvalue positiveH n a periodic, Real.exp_sub,
    Real.exp_nat_mul, Real.exp_log positiveEigenvalue]
  ring

end LeanShared.BilateralShadowingCoding
