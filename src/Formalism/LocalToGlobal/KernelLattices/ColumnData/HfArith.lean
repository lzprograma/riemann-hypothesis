module

public import Formalism.LocalToGlobal.ComplexLatticeArea
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfTrace
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterion
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfArith
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

export Formalism.ComplexLatticeArea
  (Bf Bf_swap Bf_sub_zsmul_left Bf_sub_zsmul_right cramer Bf_comb cast_toNat area_spec)

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds
open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

abbrev bb : D.host.E := D.host.sqd
abbrev be : ℂ := AR.beH D.host
abbrev ph (c : 𝓞 D.host.K) : ℂ := AR.phH D.host c
def OKc (z : ℂ) : Prop := AR.OKcH D.host z
theorem d_pos : (0 : ℝ) < D.host.d := AR.d_pos_host D.host
alias sqrt_pos := _root_.Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.sqrt_d_pos
theorem d_mod : ∃ k : ℤ, (D.host.d : ℤ) = 4 * k + 3 := AR.d_mod_host D.host
theorem phi_b : D.host.φ₀ (bb D) = be D := D.host.φ₀_mem
theorem b_sq : bb D ^ 2 = -(D.host.d : D.host.E) := AR.b_sq_host D.host
def bK : D.host.K := AR.bK_host D.host
theorem okc_of (u : 𝓞 D.host.K) : OKc D (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
  by apply _root_.UpperTheory.Reformulated.B.IntegralClosureCriterion.okc_of
theorem okc_mul {z w : ℂ} (hz : OKc D z) (hw : OKc D w) : OKc D (z * w) := AR.okc_mul_host D.host hz hw
theorem coord_eq (x y : ℤ) : ((x : ℂ) + (y : ℂ) * be D) / 2 =
    (((x : ℝ) / 2 : ℝ) : ℂ) + (((y : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := AR.coord_eq_host D.host x y
theorem good_of_okc {u : ℂ} (hu : OKc D u) : Good D (2 * u / (Real.sqrt D.host.d : ℂ)) := AR.good_of_okc_host D.host hu
theorem bK_sq : bK D ^ 2 = -(D.host.d : D.host.K) := AR.bK_sq_host D.host
def om : 𝓞 D.host.K := AR.om_host D.host
theorem ph_om : ph D (om D) = (1 + be D) / 2 := AR.ph_om_host D.host
theorem div_okc (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area (lamOf D cc δ) = Complex.normSq δ * (Real.sqrt D.host.d / 2) * m ∧
      ∀ c ∈ cc, ∀ c' ∈ cc, OKc D (starRingEnd ℂ (ph D c') * ph D c / m) :=
  AR.div_okc_host D.host cc hcc δ hδ (lamOf D cc δ) (FL.lam_mem D cc δ)
    (fun c hc => AddSubgroup.subset_closure ⟨c, hc, rfl⟩) (okc_of D)

def HYYIntRec : Prop :=
  ∀ D : Car, ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
    ∀ A ∈ YYl D L L', ∀ B ∈ YYl D L L', IsIntegral ℤ (hYY D A B)

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds
open NumberField Formalism.BasicNotions Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem HfArithRec_of_int (h : HYYIntRec) : HfArithRec := by
  intro D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'
  obtain ⟨m, hm, harea, hdiv⟩ := div_okc D cc hcc.1 δ h0
  have hh : OKc D (D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E)) :=
    okc_of D ⟨hYY D A B, h D N N' L L' hA A hA' B hB'⟩
  have hg := good_of_okc D (okc_mul D (hdiv c hc c' hc') hh)
  convert hg using 1
  have hr := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR.ratio_eq_of_area_host D.host
    (z := ph D c') (w := ph D c) h0 hm harea
  calc _ = (starRingEnd ℂ (δ * ph D c') * (δ * ph D c)) / (area (lamOf D cc δ) : ℂ) *
            D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E) := by
          simp only [ph, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR.phH]; ring
    _ = _ := by rw [hr]; ring

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
