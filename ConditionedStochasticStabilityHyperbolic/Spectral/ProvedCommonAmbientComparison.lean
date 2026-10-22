module
public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonAmbientClassicalComparison
public import LeanShared.Analysis.CommonCoreSpectralImages
public import LeanShared.Analysis.CommonAmbientStableKernels

/-! Full common-ambient spectral comparison, derived from actual compact
weak inclusion, power estimates, compact-square physical action and dense
common core. No comparison or meromorphic spectral source is supplied. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
open LeanShared
variable {A F Z Reg W : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

theorem classicalContract : ClassicalContract (A := A) (F := F) (Z := Z) (Reg := Reg) (W := W) := by
  intro P Q L a b injectiveA injectiveB actionA actionB cA cF U denseA denseF common
    coreA coreF i injectiveI compactI α R C D K hα hαR hC hD hK weak strong compactQ ρ hαρ
  have kernels (z : ℂ) (hz : ρ < ‖z‖) (k : ℕ) :
      ((P-z•1)^k).ker.map a.toLinearMap = ((Q-z•1)^k).ker.map b.toLinearMap := by
    have commonValues (v : Reg) : a (cA v) = b (cF v) :=
      congrArg (fun T : Reg →L[ℂ] Z => T v) common
    obtain ⟨n,m,stableP,stableQ,images⟩ := CommonCoreSpectralImages.exists_stable_images
      P Q L a b actionA actionB cA cF denseA denseF commonValues i compactI
      α R C D hα (hα.le.trans hαR.le) hC hD strong compactQ z (hαρ.trans hz)
    exact CommonAmbientStableKernels.map_eq P Q L a b actionA actionB injectiveA injectiveB
      z n m stableP stableQ images k
  have matchQ (z : ℂ) (hz : ρ < ‖z‖) (k : ℕ) (f : F)
      (hf : ((Q-z•1)^k) f=0) : ∃ v : A, ((P-z•1)^k) v=0 ∧ b f=a v := by
    have member : b f ∈ ((P-z•1)^k).ker.map a.toLinearMap := by
      rw [kernels z hz k]
      exact ⟨f,hf,rfl⟩
    rcases member with ⟨v,hv,same⟩
    exact ⟨v,hv,same.symm⟩
  refine ⟨?_,?_,?_⟩
  · intro f nonzero z eigen hz
    have kernel : ((Q-z•(1 : F →L[ℂ] F))^(1 : ℕ)) f=0 := by
      simp only [pow_one,sub_apply,smul_apply,one_apply_eq_self,eigen,sub_self]
    obtain ⟨v,hv,same⟩ := matchQ z hz 1 f kernel
    refine ⟨v,?_,?_,same⟩
    · intro zero
      apply nonzero
      apply injectiveB
      simp only [same,zero,map_zero]
    · exact sub_eq_zero.mp (by simpa only [pow_one,sub_apply,smul_apply,one_apply_eq_self] using hv)
  · intro z hz k f _ kernel
    exact matchQ z hz k f kernel
  · intro v nonzero z eigen hz
    have kernel : ((P-z•(1 : A →L[ℂ] A))^(1 : ℕ)) v=0 := by
      simp only [pow_one,sub_apply,smul_apply,one_apply_eq_self,eigen,sub_self]
    have member : a v ∈ ((Q-z•1)^1).ker.map b.toLinearMap := by
      rw [←kernels z hz 1]
      exact ⟨v,kernel,rfl⟩
    rcases member with ⟨f,hf,same⟩
    refine ⟨f,?_,?_,same⟩
    · intro zero
      apply nonzero
      apply injectiveA
      simp only [←same,zero,map_zero]
    · have equality : ((Q-z•(1 : F →L[ℂ] F))^(1 : ℕ)) f = 0 := hf
      exact sub_eq_zero.mp (by simpa only [pow_one,sub_apply,smul_apply,one_apply_eq_self] using equality)
end ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
