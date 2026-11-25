module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
public import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementL
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeSesquilinearFormIsHerm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExistsUnitFactorizationBounded
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.HomotheticLatticeIntegralOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ExistsWittSeriesInverseFormalGroupIso
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDict
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne

@[expose] public section

noncomputable section

namespace GlobalTheory.CurveDictionary

open NumberField Formalism.BasicNotions

theorem sgStar_lattice (L : PeriodPair) :
    Formalism.MainNotions.TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  rw [GlobalTheory.OddTheta.sgStar_eq L L.lattice.toAddSubgroup (fun _ => Iff.rfl), GlobalTheory.Mem.Col2.ThetaVec.sgStar_eq]

theorem s2_in_unramified_closure (hTor : Formalism.L2.Th1.CM.CM4) (dK : ℕ) (L : PeriodPair) (hsq : Squarefree dK) (h4 : dK % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (l : ℕ) [Fact l.Prime] (hl5 : 5 ≤ l) (hld : ¬ l ∣ dK)
    (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]) (hlam : lam ≠ 0)
    (k2 : lam ^ 4 * ι L.g₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l) (k3 : lam ^ 6 * ι L.g₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l)
    (n2 : ‖lam ^ 4 * ι L.g₂‖ ≤ 1) (n3 : ‖lam ^ 6 * ι L.g₃‖ ≤ 1)
    (nd : ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1) :
    lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  have hlp : l.Prime := Fact.out
  have hd0 : 0 < dK := by omega
  obtain ⟨S, hS, -, -, hsum⟩ := Formalism.L2.Th1.F.hasCMByIsogeny dK L hcm (-1) 2 (by simp) hd0
  obtain ⟨hst, hns⟩ := Formalism.L2.Th1.F.hasCMByStable dK L hcm (-1) 2
  rw [Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq, hns] at hsum
  have hsum' : -(2 * (dK : ℂ)) * Formalism.L2.Th1.F.s2 L = ∑ P ∈ S, L.weierstrassP P := by
    rw [← hsum]; push_cast; ring
  have hP : ∀ P ∈ S, lam ^ 2 * ι (L.weierstrassP P) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
    intro P hPS
    obtain ⟨h1, h2⟩ := hS.1 P hPS
    have h3 : (dK : ℂ) * P ∈ L.lattice := by
      have h4' := hst _ h1
      have h5 : (dK : ℂ) * P
          = -((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK)
              * ((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) * P)) := by
        rw [← mul_assoc, ← sq, Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq]; ring
      rw [h5]; exact neg_mem h4'
    exact (hTor dK L hsq h4 hcm l hl5 hld ι lam hlam k2 k3 n2 n3 nd P dK hd0 hld h3 h2).1
  have hn : ¬ l ∣ 2 * dK := by
    intro h
    rcases (Nat.Prime.dvd_mul hlp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact hld h
  have hN : ‖((2 * dK : ℕ) : ℂ_[l])‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hlp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) hn
  have hN0 : ((2 * dK : ℕ) : ℂ_[l]) ≠ 0 := by
    intro h; rw [h, norm_zero] at hN; exact zero_ne_one hN
  have key : lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L)
      = -(((2 * dK : ℕ) : ℂ_[l])⁻¹ * ∑ P ∈ S, lam ^ 2 * ι (L.weierstrassP P)) := by
    have h := congrArg ι hsum'

    rw [map_mul, map_neg, map_mul, map_sum, map_ofNat, map_natCast] at h
    rw [← Finset.mul_sum, ← h]
    push_cast
    push_cast at hN0
    have hd : (dK : ℂ_[l]) ≠ 0 := right_ne_zero_of_mul hN0
    field_simp
  rw [key]
  exact neg_mem (mul_mem (inv_mem (natCast_mem _ _)) (sum_mem fun P hPS => hP P hPS))

theorem cmLatticeInvariants_algebraic_of_goodReduction (hGood : Formalism.L2.Th1.CM.CM2) : Formalism.L2.KerInert.Sigma.InvAlg := by
  intro D cc δ hcurve hδ12 L hL
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12
  obtain ⟨-, hCM⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc hδ
  have hL' : (L.lattice : Set ℂ) = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcurve δ hδ12
    rw [← e2, ← e3]
    exact h
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1
  obtain ⟨p, hp5, hpp⟩ := Nat.exists_infinite_primes (D.host.d + 5)
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpd : ¬ p ∣ D.host.d := fun h => by have := Nat.le_of_dvd hdp.pos h; omega
  have hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    mem_algebraicClosure_iff.2
      (GlobalTheory.InertGenusOne.isAlgebraic_g2_of_hasCMBy_of_disc_eq_one hGood D.host.d L hdp.squarefree hd4 hcmby p (by omega) hpd hdisc)
  have hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    have h3sq : L.g₃ ^ 2 = (L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
    have hm : L.g₃ ^ 2 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
      rw [h3sq]
      have h27 : (27 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
        have h : ((27 : ℕ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := natCast_mem _ 27
        simpa using h
      exact div_mem (sub_mem (pow_mem hg2 3) (one_mem _)) h27
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by norm_num : 0 < 2) (mem_algebraicClosure_iff.1 hm))
  exact ⟨hg2, hg3⟩

theorem wModel_Δ_lamOf (hInv : Formalism.L2.KerInert.Sigma.InvAlg) (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) :
    (Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)).Δ = 1 := by
  have hδ0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨⟨L, hL⟩, -⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc.1 hδ0
  have hL' : (L.lattice : Set ℂ) = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
  obtain ⟨h2, h3⟩ := hInv D cc δ hcc hδ L hL
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    rw [← e2, ← e3]
    exact h
  refine GlobalTheory.EvenTheta.DatumBasic.wModel_Δ lam (by rw [e2]; exact h2) (by rw [e3]; exact h3) ?_
  unfold Formalism.MainNotions.TaylorLogMetric.discr
  rw [e2, e3]
  exact hdisc

theorem frobExists : Formalism.L2.Th1.Top.FrobExistsH := by
  intro l _ hl
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.kurFrob l (by omega)
  exact ⟨σ, hσ⟩

section Cob

open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC LTIso beLT BeRat)
open Formalism.InvariantFactorPaths.G7 (cob at1)
open Formalism.L2.KerInert.BeCob (eLT)

theorem ips {K : Type} [NormedField K] [IsUltrametricDist K] {f : PowerSeries K}
    (hf : Formalism.DworkPowerSeriesWeights.Integral (f : MvPowerSeries Unit K)) (k : ℕ) : ‖PowerSeries.coeff k f‖ ≤ 1 := hf _

end Cob

end GlobalTheory.CurveDictionary

namespace GlobalTheory.CurveDictionary

open NumberField Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1 At InertK ModelOverW)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF UnrOK IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.L2.KerInert.BeCob (eLT vLT psiLT)
open Formalism.L2.KerInert.BeCob (cc_beLT cc_lgF' lgF_eq_logF map_cob)
open Formalism.L2.KerInert.WeierstrassScaling (dict_core ePhi1_scale flog_scale isModel_scale isWq_scale scC scC_mul_uinv subst_Cmul_rescale)
open Formalism.L2.KerInert.Sigma (g_change inv_good sgSer_eq wModel_g wpReg_eq wp_sub_kur)

theorem curveDict_of_inputs (hGood : Formalism.L2.Th1.CM.CM2) (hTor : Formalism.L2.Th1.CM.CM4)
    (hS2of : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic)
    (hCW : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ MaximalUnramifiedExtension p → W.a₂ ∈ MaximalUnramifiedExtension p →
      W.a₃ ∈ MaximalUnramifiedExtension p → W.a₄ ∈ MaximalUnramifiedExtension p → W.a₆ ∈ MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ MaximalUnramifiedExtension p →
      Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]))
    (hBC : Formalism.L2.KerInert.BeCob.BeCoef) (hCE : Formalism.L2.KerInert.BeCob.CobExact)
    (hCS : Formalism.L2.KerInert.BeCob.CobSimeq) (hPT : Formalism.L2.KerInert.BeCob.PhTie)
    (hTT : Formalism.L2.KerInert.BeCob.ThetaTie)
    (hVI : ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ∀ (hLT : LTIso g) (n : ℕ),
      ‖PowerSeries.coeff n (Formalism.L2.KerInert.BeCob.vLT hLT)‖ ≤ 1) :
    Formalism.L2.KerInert.Rep.CurveDict := by
  have hInv := cmLatticeInvariants_algebraic_of_goodReduction hGood
  have hS2 := hS2of hInv
  intro D cc δ l _ g hLT hAt h5 hIn hOW
  have hp : l.Prime := Fact.out
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := id hAt
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12
  obtain ⟨⟨L, hL⟩, hCM⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  have hs := hS2 D cc δ hcurve hδ12 L hL
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  set s0 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs⟩ with hs0
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hser : Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂ =
      Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [hLg]; exact sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl
  have hW0 := wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  set εu : ℂ_[l] := ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) with hεu
  have hεne : εu ≠ 0 := Units.ne_zero _
  obtain ⟨c2, c3⟩ := g_change g.C (Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂)
  have gW2 : Formalism.L2.Th1.A.g₂ g.W = εu ^ 4 * g.lam a2 := by rw [← hW0.1]; exact c2
  have gW3 : Formalism.L2.Th1.A.g₃ g.W = εu ^ 6 * g.lam a3 := by rw [← hW0.2]; exact c3
  have hwp : Formalism.L2.Th1.A.wpReg g.W =
      PowerSeries.C (εu ^ 2) * PowerSeries.rescale εu (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [wpReg_eq, gW2, gW3]
    exact (_root_.Formalism.L2.Th1.F.series_scale ℂ_[l] (g.lam a2) (g.lam a3) εu).2.2.2.1
  set s2 : ℂ_[l] := εu ^ 2 * g.lam s0 with hs2def
  have hR : PowerSeries.rescale εu (Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂) = PowerSeries.C εu * Formalism.L2.Th1.B.sgW g.W s2 := by
    unfold Formalism.L2.Th1.B.sgW
    rw [hser, hwp]
    exact ((_root_.Formalism.L2.Th1.F.sigma_scale' ℂ_[l] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) εu).2).symm
  have hph : g.ph = Formalism.L2.Th1.B.phW g.W s2 := Formalism.L2.KerInert.Dict.formal_phase_agree l g s2 hOk hR
  have hcc0 : PowerSeries.constantCoeff g.ph = 0 := by
    rw [hph]; exact (_root_.Formalism.L2.Th1.B.Crv.curve_sigma_function_holds ℂ_[l] g.W s2).1

  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending l g.lam
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hsqf : Squarefree D.host.d := hdp.squarefree
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod l) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn
  have hsq' : ¬ ∃ a : ZMod l, a ^ 2 = -(D.host.d : ZMod l) := by
    rintro ⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩
  have hpd : ¬ l ∣ D.host.d := by
    intro h; apply hsq'; refine ⟨0, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff _ _).2 h]; ring
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1
  have hιg2 : ι L.g₂ = g.lam a2 := hι a2
  have hιg3 : ι L.g₃ = g.lam a3 := hι a3
  have hιs : ι (Formalism.L2.Th1.F.s2 L) = g.lam s0 := hι s0
  obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
  obtain ⟨w1, w2, w3, w4, w6⟩ := hOW
  obtain ⟨k2, k3, n2, n3, nd⟩ := inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
  have ks : s2 ∈ MaximalUnramifiedExtension l := by
    have k2' := k2; have k3' := k3; have n2' := n2; have n3' := n3; have nd' := nd
    rw [gW2, ← hιg2] at k2' n2'
    rw [gW3, ← hιg3] at k3' n3'
    rw [gW2, gW3, ← hιg2, ← hιg3] at nd'
    rw [hs2def, ← hιs]
    exact s2_in_unramified_closure hTor D.host.d L hsqf hd4 hcmby l h5 hpd ι εu hεne k2' k3' n2' n3' nd'
  have heW : eLT hLT ∈ Formalism.MainNotions.GL3Theta.Wp l := Formalism.L2.G.Pend.wToC_mem_Wp l _
  have he1 : ‖eLT hLT‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have ke : (eLT hLT)⁻¹ ∈ MaximalUnramifiedExtension l := inv_mem (wp_sub_kur _ heW)
  set G2 : MaximalUnramifiedExtension l := ⟨_, k2⟩ with hG2
  set G3 : MaximalUnramifiedExtension l := ⟨_, k3⟩ with hG3
  set S2 : MaximalUnramifiedExtension l := ⟨s2, ks⟩ with hS2d
  set E : MaximalUnramifiedExtension l := ⟨(eLT hLT)⁻¹, ke⟩ with hEd
  have hE1 : ‖E‖ = 1 := by
    show ‖(eLT hLT)⁻¹‖ = 1
    rw [norm_inv, he1, inv_one]
  have hth : ∀ n, ‖PowerSeries.coeff n (thetaS l G2 G3 E)‖ ≤ 1 := by
    intro n
    have hm := FAux.thetaS_map (MaximalUnramifiedExtension l).subtype (l := l) hp.two_le G2 G3 E
    rw [← FAux.norm_coe l, ← PowerSeries.coeff_map, hm]
    exact hTT l h5 g hLT hOk n

  have hgood : Formalism.L2.Th1.CM.IsGoodModel l L ι (G2 : ℂ_[l]) (G3 : ℂ_[l]) := by
    refine ⟨k2, k3, n2, n3, nd, εu, hεne, ?_, ?_⟩
    · show Formalism.L2.Th1.A.g₂ g.W = _
      rw [hιg2]; exact gW2
    · show Formalism.L2.Th1.A.g₃ g.W = _
      rw [hιg3]; exact gW3
  set c : ℂ := ι.symm εu⁻¹ with hcdef
  have hιc : ι c = εu⁻¹ := by rw [hcdef]; exact ι.apply_symm_apply _
  have hc : c ≠ 0 := by
    intro h0; rw [h0, map_zero] at hιc; exact inv_ne_zero hεne hιc.symm
  obtain ⟨-, -, -, -, -, -, hs2c, -, -, hg2c, hg3c⟩ := Formalism.L2.Th1.F.homogeneity L c hc
  have h2c : (G2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ := by
    show Formalism.L2.Th1.A.g₂ g.W = _
    rw [hg2c, map_mul, map_inv₀, map_pow, hιc, hιg2, gW2, inv_pow, inv_inv]
  have h3c : (G3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ := by
    show Formalism.L2.Th1.A.g₃ g.W = _
    rw [hg3c, map_mul, map_inv₀, map_pow, hιc, hιg3, gW3, inv_pow, inv_inv]
  have hsc : (S2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc)) := by
    show s2 = _
    rw [hs2c, map_mul, map_inv₀, map_pow, hιc, hιs, hs2def, inv_pow, inv_inv]
  have hNR : ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
      ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l G2 G3 S2 E) α := by
    intro σ hσ α hα hσα
    have hw := (sqrtKur D.host.d hsqf hd4 l h5 hsq' ι).1
    have hmem : ∀ m n : ℤ, ι ((m : ℂ) + (n : ℂ) * omegaK D.host.d) ∈ MaximalUnramifiedExtension l := by
      intro m n
      rw [map_add (f := _), map_mul, map_intCast, map_intCast]
      exact add_mem (intCast_mem _ m) (mul_mem (intCast_mem _ n) hw)
    let S : Set (MaximalUnramifiedExtension l) := {a | ∃ m n : ℤ, ¬ (l : ℤ) ∣ normInt D.host.d m n ∧
      (a : ℂ_[l]) = ι ((m : ℂ) + (n : ℂ) * omegaK D.host.d)}
    refine normUnits (MaximalUnramifiedExtension l) l σ hσ (phFF l G2 G3 S2 E) (FAux.cc_phFF (by omega) _ _ _ _) S ?_ α ?_
    · rintro a ⟨m, n, hmn, ha⟩
      exact nrDense hTor D.host.d L hsqf hd4 hcmby l h5 hpd hsq' ι G2 G3 E S2 hgood hE1 hth
        c hc h2c h3c hsc σ hσ m n hmn a ha
    · intro e he
      obtain ⟨m, n, hmn, hclose⟩ := denseOK D.host.d hsqf hd4 l h5 hsq' ι σ hσ α hα hσα e he
      exact ⟨⟨_, hmem m n⟩, ⟨m, n, hmn, rfl⟩, by simpa using hclose⟩

  have hBR : BeRat g (eLT hLT) := by
    have hphW : Formalism.MainNotions.GL3Theta.CoefWf g.ph := by
      rw [hph]
      exact hCW l g.W (wp_sub_kur _ w1) (wp_sub_kur _ w2) (wp_sub_kur _ w3) (wp_sub_kur _ w4) (wp_sub_kur _ w6) s2 ks
    have hB := hBC l g hOk ⟨w1, w2, w3, w4, w6⟩ hphW
    show BeRat g (wToC l (epOf hLT : Formalism.MainNotions.FormalGroupSystem.WW l))
    rw [← Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap l]
    exact Formalism.L2.G.Pend.beRat_of g hOk.2.2.1 hB (Formalism.L2.G.Pend.exRat_of g hOk ⟨w1, w2, w3, w4, w6⟩) _
  obtain ⟨σ0, hσ0⟩ := frobExists l h5
  obtain ⟨F0, hF0⟩ := (_root_.Formalism.InvariantFactorPaths.G7.formal_law_exists (MaximalUnramifiedExtension l) l hσ0.1 hσ0.2.2.1).1
  have tie : ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)))
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l G2 G3 S2 E))) := by
    intro F hF
    rw [hCE l g hLT hOk hBR F hF, map_cob (MaximalUnramifiedExtension l).subtype F hF.1,
      Formalism.L2.Th1.E.Joints.map_phFF (MaximalUnramifiedExtension l).subtype hp.two_le]
    refine hCS ℂ_[l] _ (by rw [MvPowerSeries.constantCoeff_map, hF.1, map_zero]) ?_ _ _ (hPT l g hLT hOk s2 hph)
    intro n
    rw [MvPowerSeries.coeff_map]
    exact hF.2.1 n

  have hlamg : g.abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := hLam
  have hΔW : g.W.Δ = εu ^ 12 := by
    show (g.C • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂).Δ = εu ^ 12
    rw [WeierstrassCurve.variableChange_Δ, hlamg,
      wModel_Δ_lamOf hInv D cc δ hcurve hδ12 g.lam, mul_one]
  have hΔ1 : ‖g.W.Δ‖ = 1 := hOk.1.2.2.2.2.2
  have hεu1 : ‖εu‖ = 1 := by
    have := hΔ1
    rw [hΔW, norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hnorm : ‖εu * (eLT hLT)⁻¹‖ = 1 := by rw [norm_mul, norm_inv, he1, hεu1, inv_one, one_mul]

  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq g.W.Δ (show 0 < 12 by norm_num)
  have hν1 : ‖ν‖ = 1 := by
    have := congrArg norm hν
    rw [norm_pow, hΔ1] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hν0 : ν ≠ 0 := by
    intro h; rw [h, norm_zero] at hν1; exact zero_ne_one hν1
  have hp2 : l ≠ 2 := by omega
  set C' := scC ν hν0 * g.C with hC'
  set wq' := PowerSeries.rescale ν⁻¹ g.wq with hwq'
  have hC'W : C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂ = scC ν hν0 • g.W := mul_smul _ _ _
  have hM : Formalism.MainNotions.TaylorLogMetric.IsModel g.lam g.abelian₂ C' :=
    isModel_scale g.lam g.abelian₂ g.C hOk.1 ν hν0 hν1 hν
  have hWq : Formalism.MainNotions.TaylorLogMetric.IsWq (C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂) wq' := by
    rw [hC'W]; exact isWq_scale ν hν0 _ _ hOk.2.1

  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set v := vLT hLT with hvdef
  set A : PowerSeries ℂ_[l] := PowerSeries.C (eLT hLT)⁻¹ * lgF ℂ_[l] l with hAdef
  have hA0 : PowerSeries.constantCoeff A = 0 := by rw [hAdef, map_mul, cc_lgF', mul_zero]
  have hAs : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have hexs : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hv0 : PowerSeries.constantCoeff v = 0 := by
    rw [hvdef, vLT]
    exact PowerSeries.constantCoeff_subst_eq_zero hA0 _ hex
  have hvs : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero' hv0
  have hvl : PowerSeries.subst v g.l = A := by
    rw [hvdef, vLT, ← hAdef, ← PowerSeries.subst_comp_subst_apply hexs hAs, hinv, PowerSeries.subst_X hAs]
  set hh : PowerSeries ℂ_[l] := PowerSeries.C ν * v with hhdef
  have hh0 : PowerSeries.constantCoeff hh = 0 := by rw [hhdef, map_mul, hv0, mul_zero]
  have hhI : ∀ n, Formalism.MainNotions.TaylorLogMetric.IsIntP (PowerSeries.coeff n hh) := by
    intro n
    unfold Formalism.MainNotions.TaylorLogMetric.IsIntP
    rw [hhdef, PowerSeries.coeff_C_mul, norm_mul, hν1, one_mul]
    exact hVI l g hOk hLT n
  have hlog : PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.flog (C' • Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂) wq') =
      PowerSeries.C (ν * (eLT hLT)⁻¹) * PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) := by
    have hs : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
    rw [hC'W, hwq', flog_scale ν hν0, ← PowerSeries.smul_eq_C_mul,
      PowerSeries.subst_smul hs, hhdef, subst_Cmul_rescale ν hν0 v _ hv0]
    change ν • PowerSeries.subst v g.l = _
    rw [hvl, hAdef, lgF_eq_logF, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul]

  set phC : PowerSeries ℂ_[l] := phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 (eLT hLT)⁻¹ with hphC
  have hphL : Formalism.L2.Th1.Top.phL l G2 G3 S2 E = phC := by
    unfold Formalism.L2.Th1.Top.phL
    rw [Formalism.L2.Th1.E.Joints.map_phFF (MaximalUnramifiedExtension l).subtype hp.two_le]
    rfl
  have hphC0 : PowerSeries.constantCoeff phC = 0 := by
    rw [← hphL]; unfold Formalism.L2.Th1.Top.phL
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega) _ _ _ _, map_zero]
  set ψ : PowerSeries ℂ_[l] := psiLT hLT with hψdef
  have hψ0 : PowerSeries.constantCoeff ψ = 0 := by
    rw [hψdef, psiLT]; exact PowerSeries.constantCoeff_subst_eq_zero hv0 _ hcc0
  have hsym := (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[l] Unit).2.1 _ _ (hPT l g hLT hOk s2 hph)
  set V : PowerSeries ℂ_[l] := Formalism.L2.Th1.C.mvExp (phC - ψ) with hVdef
  have hV : ∀ n, Formalism.MainNotions.TaylorLogMetric.IsIntP (PowerSeries.coeff n V) := fun n => ips hsym.2 n
  have hsubE : PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.ePhi1 g.lam g.abelian₂ C' wq') = Formalism.L2.Th1.C.mvExp (-ψ) := by
    rw [hC', hwq', ePhi1_scale, hhdef,
      subst_Cmul_rescale ν hν0 v _ hv0, Formalism.L2.KerInert.Dict.ePhi1_eq g s2 hOk hR, ← hph]
    have hn : PowerSeries.constantCoeff (-g.ph) = 0 := by rw [map_neg, hcc0, neg_zero]
    change PowerSeries.subst v (Formalism.L2.Th1.C.mvExp (-g.ph) : PowerSeries ℂ_[l]) = _
    rw [Formalism.L2.Th1.C.subst_mvExp hn hv0, hψdef, psiLT, ← PowerSeries.coe_substAlgHom hvs, map_neg]
  have hexp : (Formalism.L2.Th1.C.mvExp phC : PowerSeries ℂ_[l]) =
      V * (PowerSeries.subst hh (Formalism.MainNotions.TaylorLogMetric.ePhi1 g.lam g.abelian₂ C' wq'))⁻¹ := by
    have hn : PowerSeries.constantCoeff (Formalism.L2.Th1.C.mvExp (-ψ) : PowerSeries ℂ_[l]) ≠ 0 := by
      have h1 := Formalism.L2.Th1.C.constantCoeff_mvExp (show MvPowerSeries.constantCoeff (-ψ : PowerSeries ℂ_[l]) = 0 by
        rw [map_neg]; exact (neg_eq_zero.mpr hψ0))
      intro h0
      exact one_ne_zero (h1.symm.trans h0)
    have hinvE : (Formalism.L2.Th1.C.mvExp ψ : PowerSeries ℂ_[l]) = (Formalism.L2.Th1.C.mvExp (-ψ) : PowerSeries ℂ_[l])⁻¹ :=
      (PowerSeries.eq_inv_iff_mul_eq_one hn).mpr (Formalism.L2.Th1.C.mvExp_mul_neg hψ0)
    rw [hsubE, ← hinvE, hVdef]
    exact (Formalism.L2.Th1.C.mvExp_sub_mul hphC0 hψ0).symm
  have hcEq : (((C'.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l])) * (ν * (eLT hLT)⁻¹) = εu * (eLT hLT)⁻¹ := by
    rw [hC', scC_mul_uinv, ← hεu]
    field_simp
  refine ⟨G2, G3, E, S2, rfl, rfl, rfl, hR, hnorm,
    ⟨n2, n3, hE1, hth, hNR, cc_beLT hOk hLT hBR hcc0, F0, hF0, tie F0 hF0⟩, ?_⟩
  intro D'
  refine ⟨C', wq', hM, hWq, ?_⟩
  intro N N' r b G hInt
  have key := dict_core hp2 D' g.lam g.abelian₂ C' wq' hh hh0 hhI (ν * (eLT hLT)⁻¹) hlog
    phC V hphC0 hV hexp b G hInt
  rw [hcEq] at key
  rw [hphL]
  exact key

end GlobalTheory.CurveDictionary
