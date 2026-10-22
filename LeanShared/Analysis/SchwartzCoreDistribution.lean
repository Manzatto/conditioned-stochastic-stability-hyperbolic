module
public import LeanShared.Analysis.CompletedCorePairingBounds
public import LeanShared.Analysis.LaplacianSupportedTestJet
public import LeanShared.Analysis.SchwartzAmbientBlocks

/-! A proved dyadic core pairing estimate constructs the finite-order
Schwartz distribution pairing on its actual completed norm. -/
public noncomputable section
open Set
open scoped SchwartzMap
namespace LeanShared.SchwartzCoreDistribution
variable {E B : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  (K : Set E) (q : SchwartzJetSpace.supportedCore K→ₗ[ℂ]B)
  (C : ℝ) (n m : ℕ)
  (estimate : ∀ (f : SchwartzJetSpace.supportedCore K) (test : 𝓢(E,ℂ)),
    ‖ConeFourierBlocks.integralPairing f.val test‖ ≤ C*‖q f‖*
      (ObliqueSchwartzDecay.seminorm m test+
        ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n test)))

include estimate in
theorem bounded : ∀ test,∃ coefficient:ℝ,∀ f,
    ‖SchwartzAmbientBlocks.pairing K f test‖ ≤ coefficient*‖q f‖ := by
  intro test
  refine ⟨C*(ObliqueSchwartzDecay.seminorm m test+
    ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n test)),fun f=>?_⟩
  exact (estimate f test).trans_eq (mul_right_comm _ _ _)

@[expose] def pairing : DyadicCompletion.closedCore q→ₗ[ℂ](𝓢(E,ℂ)→ₗ[ℂ]ℂ) :=
  CompletedCorePairing.pairing q (SchwartzAmbientBlocks.pairing K)
    (bounded K q C n m estimate)

theorem core (f : SchwartzJetSpace.supportedCore K) (test : 𝓢(E,ℂ)) :
    pairing K q C n m estimate (DyadicCompletion.coreLift q f) test=
      ConeFourierBlocks.integralPairing f.val test :=
  CompletedCorePairing.pairing_core q (SchwartzAmbientBlocks.pairing K)
    (bounded K q C n m estimate) f test

theorem finite_order_bound {ι:Type*} [Fintype ι] (basis:OrthonormalBasis ι ℝ E)
    (L:Set E) (closed:IsClosed L) (R:ℝ) (nonnegative:0≤R)
    (radius:∀x∈L,‖x‖≤R) (positive:0≤C)
    (z:DyadicCompletion.closedCore q) (test:𝓢(E,ℂ)) (supported:∀x∉L,test x=0) :
    ‖pairing K q C n m estimate z test‖ ≤
      (C*((1+R)^m*(Fintype.card (LaplacianFiniteJet.Index ι 0)+
        Fintype.card (LaplacianFiniteJet.Index ι n))))*‖z‖*
          ‖SchwartzJetSpace.jetMap L (LaplacianFiniteJet.testWords basis n) test‖ :=
  CompletedCorePairing.pairing_order_bound q (SchwartzAmbientBlocks.pairing K)
    (bounded K q C n m estimate) test C
    ((1+R)^m*(Fintype.card (LaplacianFiniteJet.Index ι 0)+
      Fintype.card (LaplacianFiniteJet.Index ι n)))
    ‖SchwartzJetSpace.jetMap L (LaplacianFiniteJet.testWords basis n) test‖
    positive (ObliqueSchwartzDecay.seminorm m test+
      ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n test))
    (fun f=>estimate f test)
    (LaplacianFiniteJet.test_seminorm_bound basis n m L closed R nonnegative radius test supported) z
end LeanShared.SchwartzCoreDistribution
