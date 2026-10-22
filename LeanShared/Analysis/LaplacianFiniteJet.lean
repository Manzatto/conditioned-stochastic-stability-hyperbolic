module
public import LeanShared.Analysis.FourierSchwartzLaplacian
public import LeanShared.Analysis.SchwartzJetSpace
public import LeanShared.Analysis.PolynomialSchwartzSeminorm
import Mathlib.Analysis.Normed.Group.Constructions

/-! Every finite Laplacian power is an explicit finite sum of actual
directional derivative words, and is controlled by the literal finite jet. -/
public noncomputable section
open Set
open scoped SchwartzMap LineDeriv Laplacian BoundedContinuousFunction
namespace LeanShared.LaplacianFiniteJet
universe u
@[expose] def Index (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => ι × Index ι n
instance indexFintype {ι : Type*} [Fintype ι] : (n : ℕ) → Fintype (Index ι n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
    let _ : Fintype (Index ι n) := indexFintype n
    exact inferInstanceAs (Fintype (ι × Index ι n))
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι]
@[expose] def word (b : ι → E) : (n : ℕ) → Index ι n → List E
  | 0,_ => []
  | n+1,j => b j.1 :: b j.1 :: word b n j.2

omit [MeasurableSpace E] [BorelSpace E] in
theorem expansion (b : OrthonormalBasis ι ℝ E) (n : ℕ) (f : 𝓢(E,ℂ)) :
    FourierSchwartzLaplacian.power n f =
      ∑ j : Index ι n, SchwartzJetSpace.wordDerivative (word b n j) f := by
  induction n with
  | zero =>
    change f = ∑ _j : PUnit, f
    simp
  | succ n ih =>
    change (fun g : 𝓢(E,ℂ) => Δ g)^[n+1] f = _
    rw [Function.iterate_succ_apply']
    change Δ (FourierSchwartzLaplacian.power n f) = _
    rw [SchwartzMap.laplacian_eq_sum b,ih]
    simp only [LineDeriv.lineDerivOp_sum]
    convert! (Fintype.sum_prod_type (fun j : ι × Index ι n =>
        ∂_{b j.1} (∂_{b j.1} (SchwartzJetSpace.wordDerivative (word b n j.2) f)))).symm using 1

omit [MeasurableSpace E] [BorelSpace E] in
theorem jet_bound (b : OrthonormalBasis ι ℝ E) (n : ℕ) (K : Set E)
    (f : 𝓢(E,ℂ)) (x : K) :
    ‖FourierSchwartzLaplacian.power n f x‖ ≤
      Fintype.card (Index ι n)*‖SchwartzJetSpace.jetMap K (word b n) f‖ := by
  rw [expansion b n f,sum_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Index ι n, ‖SchwartzJetSpace.jetMap K (word b n) f‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact ((SchwartzJetSpace.jetMap K (word b n) f j).norm_coe_le_norm x).trans
        (norm_le_pi_norm _ j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
end LeanShared.LaplacianFiniteJet
