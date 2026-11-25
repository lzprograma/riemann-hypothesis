module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegree
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QbridgeOfNumGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumPf
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFunctionalFiniteIntegralityBound
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmValueLineLengthConjEq
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LamDegreeParameters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ModelsAtOfGoodLevel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NdegLineOptionLe
import Formalism.LocalToGlobal.ProjectiveLattices.RecConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalQuotientRank
public import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormCmArcCoefficientFunctionalLe
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar

section
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.RunNum

theorem sum_extendByZero_fin_eq_sum_of_eq {p m : ℕ} (f : Fin p → ℕ) (h : m = p) : ∑ i : Fin m, ext0 f i = ∑ i, f i := by
  subst h
  exact Finset.sum_congr rfl fun i _ => by simp [ext0]

theorem conj_rt_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (τ : E →+* ℂ)
    (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h'
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by
    have h0 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h'
    rwa [h] at h0
  have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, h2] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem absA_wtA {D : D7} (T : Core D) (j : ℕ) (hD : IsDatW D j (T.Q.Dw j)) (hH : T.Q.PinHost)
    (w : WeightFamilies.Wt D j) :
    absA (T.Q.Dw j) (wtA w) = ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  classical
  simp only [absA, wtA]
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.sum_add_distrib]
  have ht := hH.2.2.2 t
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.sum_eq_single (DV.tauEmb D t)]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum_of_eq _ (by rw [← hD.1]; simp [Datum.mult, ht])
    · intro b _ hb; simp [hb]
    · simp
  · rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum_of_eq _ (by rw [← hD.2.1]; simp [Datum.mult, conj_rt_ne _ _ ht])
    · intro b _ hb; simp [hb]
    · simp

theorem absA_add_le_size {D : D7} (T : Core D) (hp : T.Q.Pins) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) :
    (absA (T.Q.Dw j) (wtA w) : ℝ) + (D.R.f : ℝ) * D.R.r * w.n ≤ w.size := by
  rw [absA_wtA T j (hp.2.2.2 j hj) hp.1 w]
  unfold WeightFamilies.Wt.size
  push_cast
  have h1 : (1 : ℝ) ≤ max ((D.R.sigW j).2 : ℝ) 1 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
  nlinarith

theorem pnorm_le_sup {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type} [Fintype Comp]
    (X : Comp → Data E r) (la) {P : FDSec X} (hP : P ∈ holSub X la) (p : FPt X) :
    (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ Formalism.L2.Pj.supN X la P := by
  unfold Formalism.L2.Pj.supN
  rw [← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]
  exact le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p

theorem one_le_LaAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : 1 ≤ LaAt D j ka CR Tt cc :=
  le_max_left _ _

theorem archimedeanTerm_nonneg (E : Type) [Field E] [NumberField E] {r : ℕ} (hr : 1 ≤ r) {La : ℝ} (hLa : 1 ≤ La) (c₁ : ℝ) :
    0 ≤ archP E r La c₁ := by
  unfold archP
  have h1 : 0 ≤ Real.log (max 1 c₁) := Real.log_nonneg (le_max_left _ _)
  have h2 : 0 ≤ Real.log La := Real.log_nonneg hLa
  have h3 : 0 ≤ Real.log (rdE E) := by
    refine Real.log_nonneg (Real.one_le_rpow ?_ (by positivity))
    unfold dE
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have h4 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  linarith

theorem arch_good (hK : Known) {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hG : GlobalTheory.RunIn.GamAt T) (hj : InR D j) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) (hd : Std d)
    (s : CMIn d.a d.e d.th d.jj (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j))
    (em : K₁ →+* ℂ) (hem : GoodEmb T.Q.c (em.comp (algebraMap T.Q.c.F K₁))) (F : (recB h).Cusp j ka) :
    ‖em (cfOf d.yF d.μ d.jj F.1)‖ * (s.valLine d.μ ka.n).n em ≤
      (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F * Real.exp (CarchAt D j ka CR Tt cc) := by
  obtain ⟨-, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hnum j hj
  have hFc : F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n := cutR_le T.C j ka F.2
  have hS : (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F =
      supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (em.comp (algebraMap T.Q.c.F K₁)) (wtA ka) ka.n F.1 := by
    change cutN T.C T.Ns j ka _ F = _
    unfold cutN Core.Ns
    rw [if_pos hj, goodOf, if_pos hem]
  have h0 := (recB h).supN_nonneg j ka (em.comp (algebraMap T.Q.c.F K₁)) F
  have hb := _root_.GlobalTheory.ArchCM.norm_cfOf_le hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s em D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (xiR D) ((recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F)
    (wtA ka) ka.n hd (one_le_LaAt D j ka CR Tt cc) hem (h.unf j hj _ hem) (h.xiAbs j hj _ hem) (dom_wtA ka)
    (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) _ _ (hG j hj _ hem)
      (h.chiTriv j hj _ hem _ _ (dom_wtA ka)))
    F.1 (cusp_le_sec _ _ _ _ _ hFc) h0 (by
      intro k y hy
      rw [hS]
      exact mul_le_mul_of_nonneg_left
        (pnorm_le_sup _ _ (((mem_cusp _ _ _ _ _ _).1 hFc).2 _ hem) ⟨k, ⟨y, hy⟩⟩) (lieFac_pos _ _ _).le)
  refine hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0)
  unfold CarchAt
  have h1 := absA_add_le_size T h.pins j hj ka
  have h2 : (fdeg D.host.E : ℝ) = D.R.f := by
    unfold fdeg
    rw [hf, Nat.mul_div_cancel_left _ two_pos]
  have h3 : (D.R.f : ℝ) * ka.n ≤ (D.R.f : ℝ) * D.R.r * ka.n := by
    have : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
    have h4 : (0 : ℝ) ≤ (D.R.f : ℝ) * ka.n := by positivity
    nlinarith
  rw [h2]
  have h5 := archimedeanTerm_nonneg D.host.E hr (one_le_LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j)
  exact add_le_add_right (mul_le_mul_of_nonneg_left (by linarith) h5) _

theorem arch_all (hK : Known) {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hG : GlobalTheory.RunIn.GamAt T) (hj : InR D j) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) (hd : Std d)
    (s : CMIn d.a d.e d.th d.jj (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j))
    (em : K₁ →+* ℂ) (F : (recB h).Cusp j ka) :
    ‖em (cfOf d.yF d.μ d.jj F.1)‖ * (s.valLine d.μ ka.n).n em ≤
      (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F * Real.exp (CarchAt D j ka CR Tt cc) := by
  by_cases hem : GoodEmb T.Q.c (em.comp (algebraMap T.Q.c.F K₁))
  · exact arch_good hK h j ka CR Tt cc hG hj K₁ d hd s em hem F
  · have hg := goodEmb_goodOf T.Q.c (em.comp (algebraMap T.Q.c.F K₁))
    rw [goodOf, if_neg hem] at hg
    have h1 := arch_good hK h j ka CR Tt cc hG hj K₁ d hd s ((starRingEnd ℂ).comp em) hg F
    rw [_root_.GlobalTheory.ArcCM.valLine_conj hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s d.μ ka.n em, RingHom.comp_assoc, recB_supN_conj] at h1
    simpa using h1

end GlobalTheory.ArcCM.RunNum

namespace GlobalTheory.ArcCM

open RunNum

end GlobalTheory.ArcCM
end
end
end


@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem room_of_bounds {z k Ch Ah C₀ A₀ Cd Ad Carch Bdeg lρ beSum : ℝ} (hz : 1 ≤ z) (hk : 0 ≤ k) (hCh : 0 ≤ Ch)
    (hC₀ : 0 ≤ C₀) (hCd : 0 ≤ Cd) (h1 : Carch ≤ C₀ * z ^ A₀ * k) (h2 : Bdeg ≤ C₀ * z ^ A₀ * k)
    (h3 : lρ ≤ Cd * z ^ Ad * k) (h4 : beSum ≤ C₀ * z ^ A₀ * k) :
    Ch * z ^ Ah * k + Carch + Bdeg + lρ / 2 ≤ (Ch + 3 * C₀ + Cd) * z ^ (max Ah (max A₀ Ad)) * k ∧
      beSum ≤ (Ch + 3 * C₀ + Cd) * z ^ (max Ah (max A₀ Ad)) * k := by
  set Ac := max Ah (max A₀ Ad)
  have hmono : ∀ A, A ≤ Ac → z ^ A ≤ z ^ Ac := fun A hA => Real.rpow_le_rpow_of_exponent_le hz hA
  have hAh : z ^ Ah ≤ z ^ Ac := hmono _ (le_max_left _ _)
  have hA₀ : z ^ A₀ ≤ z ^ Ac := hmono _ (le_trans (le_max_left _ _) (le_max_right _ _))
  have hAd : z ^ Ad ≤ z ^ Ac := hmono _ (le_trans (le_max_right _ _) (le_max_right _ _))
  have hzA : 0 ≤ z ^ Ac := Real.rpow_nonneg (by linarith) _
  have e0 : Ch * z ^ Ah * k ≤ Ch * z ^ Ac * k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAh hCh) hk
  have e1 : C₀ * z ^ A₀ * k ≤ C₀ * z ^ Ac * k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA₀ hC₀) hk
  have e2 : Cd * z ^ Ad * k ≤ Cd * z ^ Ac * k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAd hCd) hk
  have p0 : 0 ≤ Ch * z ^ Ac * k := mul_nonneg (mul_nonneg hCh hzA) hk
  have p1 : 0 ≤ C₀ * z ^ Ac * k := mul_nonneg (mul_nonneg hC₀ hzA) hk
  have p2 : 0 ≤ Cd * z ^ Ac * k := mul_nonneg (mul_nonneg hCd hzA) hk
  have e : (Ch + 3 * C₀ + Cd) * z ^ Ac * k = Ch * z ^ Ac * k + 3 * (C₀ * z ^ Ac * k) + Cd * z ^ Ac * k := by ring
  rw [e]
  constructor <;> linarith

theorem log₂ {D : D7} (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hlat : Submodule.IsLattice B.KO (B.Mlat j ka)) :
    Real.log (WeightFamilies.rhoP B CR Tt cc j ka : ℝ) ≤ Real.log (Module.finrank B.KO (B.Cusp j ka) : ℝ) := by
  have hrk := LocalQuotientRank.rank_quot (F := B.KO) (B.Mlat j ka) hlat.fg
    (WeightFamilies.MggK B CR Tt cc j ka)
  have hdim : WeightFamilies.rhoP B CR Tt cc j ka ≤ Module.finrank B.KO (B.Cusp j ka) :=
    (hrk ▸ Nat.le_add_right _ _).trans (Submodule.finrank_le _)
  rcases Nat.eq_zero_or_pos (WeightFamilies.rhoP B CR Tt cc j ka) with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hdim)

theorem qat_of_kill_detect : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D) (Ck Ch Ah C₀ A₀ Cd Ad : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h) j ka → KillQ h j ka CR Tt cc → DetectQ h j ka CR Tt cc → 1 ≤ zBase large₂ → 0 ≤ C₀ → 0 ≤ Cd → RoomAt large₂ j ka CR Tt cc C₀ A₀ →
    Real.log (@Module.finrank T.Q.c.F ((recB h).Cusp j ka) _
      ((recB h).acgC j ka).toAddCommMonoid ((recB h).modC j ka) : ℝ) ≤
      WeightFamilies.PPv D large₂ Cd Ad * ka.size →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.QAt large₂ (recB h) j ka CR Ck Ch Ah (Ch + 3 * C₀ + Cd) (max Ah (max A₀ Ad)) Tt cc := by
  intro hK D T h j ka CR Tt cc large₂ Ck Ch Ah C₀ A₀ Cd Ad hG hj hjm hlat hkill hdet hz hC₀ hCd hroom hdim
  intro hCR hOb hn hlast hsize hT hc hTc
  have hzpos : 0 < zBase large₂ := by linarith
  have hCh : 0 ≤ Ch := by
    have h1 : (1 : ℝ) ≤ WeightFamilies.degO (recB h) := by
      unfold WeightFamilies.degO
      exact_mod_cast Module.finrank_pos
    have h2 : 0 ≤ Ch * zBase large₂ ^ Ah := (Real.log_nonneg h1).trans hOb.1
    exact nonneg_of_mul_nonneg_left h2 (Real.rpow_pos_of_pos hzpos _)
  have hA : (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka) : ℝ) ≤ ka.size := by
    have h1 := absA_add_le_size T h.pins hj ka
    have h2 : (0 : ℝ) ≤ (fdeg D.host.E : ℝ) * ka.n := by positivity
    linarith
  have hk : (0 : ℝ) ≤ ka.size := (Nat.cast_nonneg _).trans hA
  have hnpos : 0 < nAt D j ka CR Tt cc := Nat.succ_pos _
  obtain ⟨hfin, hsum⟩ := beSum_holds D.host.E (recB h).KO (nAt D j ka CR Tt cc)
    (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka)) hnpos
  have hP₀ : 0 ≤ C₀ * zBase large₂ ^ A₀ := mul_nonneg hC₀ (Real.rpow_pos_of_pos hzpos _).le
  have hsum' := hsum.trans ((mul_le_mul_of_nonneg_right hroom.2.2 (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hA hP₀))
  have hlog := log₂ (recB h) j ka CR Tt cc hlat.toIsLattice
  obtain ⟨hr1, hr2⟩ := room_of_bounds (Ah := Ah) hz hk hCh hC₀ hCd hroom.1 hroom.2.1 (hlog.trans hdim) hsum'
  refine qat_of_bridge' large₂ (recB h) j ka CR Ck Ch Ah _ _ Tt cc hlat
    (qbridge_of_numGood D large₂ (recB h) j ka CR Ch Ah _ _ Tt cc
      (beOf D.host.E (nAt D j ka CR Tt cc) (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka)))
      (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) hlat (fun la => ?_) hfin hr2
      (recB_supN_conj h j ka) hr1 fun F hF => ?_) hCR hOb hn hlast hsize hT hc hTc
  · unfold beOf
    positivity
  · by_contra hno
    refine hF (hdet F fun K₁ i1 i2 i3 d hd => ?_)
    by_contra hne
    have hle : cutR T.C j ka ≤ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n :=
      (cutR_le T.C j ka).trans (cusp_le_sec _ _ _ _ _)
    obtain ⟨⟨ψ, hψ⟩, hdeg⟩ :=
      cfOf_linear_and_degree hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n
    let φ := ψ.comp (Submodule.inclusion hle)
    have hφ : ∀ G : (recB h).Cusp j ka, φ G = cfOf d.yF d.μ d.jj G.1 := fun G => hψ _
    refine hno ⟨K₁, i1, i2, i3, φ, fun G hGm => ?_, ?_, ?_⟩
    · exact (hφ G).trans (hkill K₁ d hd G hGm)
    · exact fun h0 => hne ((hφ F).symm.trans h0)
    · obtain ⟨hstd, ⟨s⟩⟩ := hd
      obtain ⟨hgood, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
      obtain ⟨hpq, hr, -⟩ := hnum j hj
      have hLa := RunNum.one_le_LaAt D j ka CR Tt cc
      have hc : 0 ≤ pDeg large₂.logOm + (1 / 2) * Real.log (LaAt D j ka CR Tt cc) := by
        have := Real.log_nonneg hLa
        unfold pDeg
        positivity
      have hμ := hdeg F.1 (hle F.2) hne
      obtain ⟨hN, hNd⟩ := valLine_ndeg_le hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s large₂.logOm d.μ ka.n hLa
        (lamDegSt_logOm₂ hK D T large₂ h.pins)
      refine ⟨s.valLine d.μ ka.n, hN, hNd.trans ?_,
        _root_.GlobalTheory.ArcCM.valLine_conj hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s _ _, ?_, ?_⟩
      · unfold BdegAt
        refine mul_le_mul_of_nonneg_left ?_ hc
        rw [hμ, hf, hpq, Nat.mul_div_cancel_left _ two_pos]
        push_cast
        exact RunNum.absA_add_le_size T h.pins j hj ka
      · intro la w hw G hGm hne'
        rw [hφ] at hne' ⊢
        exact _root_.GlobalTheory.ArcCM.cfOf_fin_bound hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s
          (modelsAt_of_good_level hK _ _ _ _ _ _ (hpq ▸ hr) hgood) hstd hLa la w hw (wtA ka) ka.n G.1
          ⟨hle G.2, fun v hv => hGm la v hv⟩ hne'
      · intro em G _ hne'
        have hpos : 0 < (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) G := by
          refine lt_of_le_of_ne ((recB h).supN_nonneg j ka _ G) fun h0 => hne' ?_
          rw [((recB h).supN_eq_zero j ka _ G).1 h0.symm]
          exact map_zero _
        have harch := RunNum.arch_all hK h j ka CR Tt cc hG hj K₁ d hstd s em G
        rw [hφ] at hne' ⊢
        have hnorm : 0 < ‖em (cfOf d.yF d.μ d.jj G.1)‖ := norm_pos_iff.2 ((map_ne_zero em).2 hne')
        have hlog := Real.log_le_log (mul_pos hnorm (hN.2 em)) harch
        rwa [Real.log_mul hnorm.ne' (hN.2 em).ne', Real.log_mul hpos.ne' (Real.exp_pos _).ne',
          Real.log_exp] at hlog

end GlobalTheory.ArcCM
