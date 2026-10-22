module
public import LeanShared.Analysis.SupportedSmoothSymbolFamily
public import LeanShared.Analysis.SmoothNonstationarySymbol
import Mathlib.Tactic

/-! Uniform actual normalized nonstationary symbols for all bounded
dyadic frequency ratios. The ratios enter a compact coefficient parameter
set, so the constructed constants do not depend on their chosen values. -/
public noncomputable section
open Set
open scoped ContDiff BoundedContinuousFunction
namespace LeanShared.NormalizedNonstationarySymbolFamily
variable {E Z:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z]

theorem exists_family {X P:Type*} [PseudoMetricSpace X]
    {δ D H a:ℝ} (positive:0<δ) (hD:0≤D) (hH:0≤H) (ha:0<a)
    (v:E) (n:ℕ) (decode:Z→L[ℝ](E × E))
    (A:P→X→E→L[ℝ]E) (value:∀p x,‖A p x‖≤D)
    (holder:∀p x y,‖A p x-A p y‖≤H*dist x y^a)
    (s t:P→ℝ) (hs:∀p,‖s p‖≤1) (ht:∀p,‖t p‖≤1)
    (χ:Z→ℂ) (smoothχ:ContDiff ℝ ∞ χ) (compactχ:HasCompactSupport χ):
    ∃B C:ℝ,0≤B ∧ 0≤C ∧
      ∃q:P→X→ᵇ(SupportedFiniteJetSpace.space (Z:=Z) n (tsupport χ)),
        (∀p x z,(BoundedFiniteJetSpace.construct n (F:=ℂ)).physical (q p x).val z=
          χ z*(SmoothNonstationarySymbol.coefficient positive v
            (A p x,(s p • (decode z).1,t p • (decode z).2)):ℂ)) ∧
        (∀p,‖q p‖≤B) ∧∀p x y,‖q p x-q p y‖≤C*dist x y^a:=by
  let V:Type:=(E→L[ℝ]E) × (ℝ × ℝ)
  let ψ:V × Z→ℂ:=fun p=>(SmoothNonstationarySymbol.coefficient positive v
    (p.1.1,(p.1.2.1 • (decode p.2).1,p.1.2.2 • (decode p.2).2)):ℂ)
  have smoothψ:ContDiff ℝ ∞ ψ:=by
    have ca:ContDiff ℝ ∞ (fun p:V × Z=>p.1.1):=contDiff_fst.fst
    have cs:ContDiff ℝ ∞ (fun p:V × Z=>p.1.2.1):=contDiff_fst.snd.fst
    have ct:ContDiff ℝ ∞ (fun p:V × Z=>p.1.2.2):=contDiff_fst.snd.snd
    have cz:ContDiff ℝ ∞ (fun p:V × Z=>decode p.2):=decode.contDiff.comp contDiff_snd
    exact Complex.ofRealCLM.contDiff.comp ((SmoothNonstationarySymbol.smooth positive v).comp
      (ca.prodMk ((cs.smul cz.fst).prodMk (ct.smul cz.snd))))
  let parameters:P→X→V:=fun p x=>(A p x,(s p,t p))
  have bounded (p:P) (x:X):‖parameters p x‖≤D+1:=by
    change max ‖A p x‖ (max ‖s p‖ ‖t p‖)≤D+1
    exact max_le ((value p x).trans (le_add_of_nonneg_right zero_le_one))
      ((max_le (hs p) (ht p)).trans (le_add_of_nonneg_left hD))
  have increments (p:P) (x y:X):‖parameters p x-parameters p y‖≤H*dist x y^a:=by
    change max ‖A p x-A p y‖ (max ‖s p-s p‖ ‖t p-t p‖)≤_
    simpa only [sub_self,norm_zero,max_self,max_eq_left (norm_nonneg _)] using holder p x y
  exact SupportedSmoothSymbolFamily.exists_family ψ smoothψ (by positivity : 0≤D+1) hH ha n
    parameters bounded increments χ smoothχ compactχ
end LeanShared.NormalizedNonstationarySymbolFamily
