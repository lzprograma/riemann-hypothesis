module

public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisationsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GalTrans

section Cong
variable {X : Type} [AddCommGroup X]

theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨-w, by rw [hw, smul_neg]; abel⟩

theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  exact ⟨w' + w, by rw [hw, hw', smul_add]; abel⟩

theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, by rw [hw, map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.mp h
  change N • w = -x + y at hw
  refine ⟨-w, ?_⟩
  rw [smul_neg, hw]
  abel

theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  obtain ⟨w, hw⟩ := h
  refine QuotientAddGroup.eq.mpr ⟨-w, ?_⟩
  change N • (-w) = -x + y
  rw [hw, smul_neg]
  abel
end Cong


open MonObj in
theorem compare {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} {y₁ : S'.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (l : u.Lab)
    (l' : u'.Lab) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left)
    (ha : IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a)
    (ha' : IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a')
    (hL : LBIso P₀.L (u.A.L.pull a)) (hL' : LBIso P₀.L (u'.A.L.pull a')) :
    ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ, l'.q (e χ) = l.q χ) ∧
      (∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A)
        (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → x ^ m = 1 → x' ^ m = 1 → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left →
        w ≫ a' = x'.left → ∃ pk pk', QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧
          QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' ∧ CongMod m pk'.y (e pk.y)) ∧
      ∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), 1 ≤ m →
        QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) m)
          (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left),
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧ x ^ m = 1 ∧ w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧
          w ≫ a' = x'.left ∧ CongMod m pk'.y (e pk.y) := by
  obtain ⟨e, hps, hcg⟩ := _root_.GlobalTheory.UnifTorsK.main S S' ρ ρ' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI := _root_.GlobalTheory.ZH.WeightZeroUnit.charZero u
  haveI := _root_.GlobalTheory.ZH.WeightZeroUnit.charZero u'
  refine ⟨e, fun χ => ?_, fun m x x' w hm hx hx' hw hwa hwa' => ?_, fun m pk' x' hm hpk' => ?_⟩
  · have h1 := (hps χ _).1 (l.q_eq χ)
    have h2 := l'.q_eq (e χ)
    have h3 := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 h1)
    linarith
  · obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨f', hf1', hf2', -⟩ := GlobalTheory.ZH.uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    obtain ⟨pk', rfl⟩ := hf2' x' hx'
    have q1 := (hf1 pk (f pk)).2 rfl
    have q2 := (hf1' pk' (f' pk')).2 rfl
    exact ⟨pk, pk', q1, q2, hcg m pk pk' _ _ w hm q1 q2 hw hwa hwa'⟩
  · have hx' : x' ^ m = 1 := by
      have h0 := hpk'
      unfold QkToAkU at h0
      obtain ⟨w0, hw0⟩ := u'.U.ext
      have h1 := h0 w0 hw0
      unfold QkToAk at h1
      exact h1.1
    obtain ⟨w, x, hw, hwa', hwa, hx⟩ :=
      GlobalTheory.PtTrans.ptTrans (PadicAlgCl p) u'.A u.A P₀ a' a ha' ha m x' hx'
    obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    have q1 := (hf1 pk (f pk)).2 rfl
    exact ⟨pk, f pk, w, q1, hx, hw, hwa, hwa', hcg m pk pk' _ _ w hm q1 hpk' hw hwa hwa'⟩


end GlobalTheory.Poinc.GalTrans
