module

public import ReciprocityTheory.GaloisValuations.Global
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

noncomputable section

namespace GlobalTheory.ParamRepCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped Pointwise

section Inertia

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
private lemma valuation_smul_smul_lt_one_iff (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (B : ValuationSubring Ω) (y : Ω) :
    (h • B).valuation (h • y) < 1 ↔ B.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.smul_mem_pointwise_smul_iff,
    ← smul_inv'', ValuationSubring.smul_mem_pointwise_smul_iff]
  simp


open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
theorem _root_.GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq {A A' : ValuationSubring Ω} {g σ : _root_.Formalism.ConjugateSelfDual.G F Ω}
    (hg : g • A = A') (hσ : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A') : g⁻¹ * σ * g ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A := by
  subst hg
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hdec ⊢
    rw [mul_smul, mul_smul, hdec, inv_smul_smul]
  · rw [← valuation_smul_smul_lt_one_iff g]
    have hx' : (g • A).valuation (g • x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      exact ValuationSubring.smul_mem_pointwise_smul g x A hx
    have := hval (g • x) hx'
    convert this using 2
    rw [smul_sub]
    simp [AlgEquiv.smul_def]

end Inertia

end GlobalTheory.ParamRepCompare

end
