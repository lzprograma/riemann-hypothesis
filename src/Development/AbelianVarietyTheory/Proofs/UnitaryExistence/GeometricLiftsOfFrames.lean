module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdmissibleFalseIffFirstInvariant
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

@[expose] public section

noncomputable section

namespace GlobalTheory.LevelCoverCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

section Calc

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {q : Y ⟶ X} {q' : Y' ⟶ X'} {pm : Y' ⟶ Y}

end Calc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Half

end Half

variable {Xo : Moduli D l} {c : Coeff l}

section Cover

variable {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a) (n : ℕ) (nab₂ : NabV C.Xo₂ C.c₂) (f : Rul C.Xo₂ C.c₂)
  (φ : (Fin n → LevQ D a.l₂) → c.F)

end Cover

section Rule

def fnRule (g : Γ(Xo.XF c, ⊤)) : Rul Xo c := fun _ y => fnAt (basePt y) g

theorem fnAt_comp {X : Scheme.{0}} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (y : Sp S ⟶ X) (g : Γ(X, ⊤)) :
    fnAt (spMap ψ ≫ y) g = ψ (fnAt y g) := by
  have e := congrArg (fun k => k.hom (y.appTop.hom g)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

theorem basePt_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {ψ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap ψ y z) : basePt z = spMap ψ.toRingHom ≫ basePt y := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
  · rw [Category.assoc, basePt, basePt, pullback.lift_snd, pullback.lift_snd,
      GlobalTheory.Frames.FramedBaseChange.spMap_comp_spMap]
    exact congrArg spMap ψ.comp_algebraMap.symm

theorem fnRule_mem (g : Γ(Xo.XF c, ⊤)) : fnRule g ∈ sec Xo c 0 0 := by
  refine ⟨fun p q ψ y z h => ?_, fun p t y y' h => ?_⟩
  · change fnAt (basePt z) g = ψ (fnAt (basePt y) g)
    rw [basePt_frMap h, fnAt_comp]
    rfl
  · have e : basePt y' = basePt y := by
      refine pullback.hom_ext ?_ ?_
      · rw [basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
      · rw [basePt, basePt, pullback.lift_snd, pullback.lift_snd]
    have e' : wchar (ex D 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
    change fnAt (basePt y') g = _ * fnAt (basePt y) g
    rw [e, e', _root_.one_mul]

theorem evR_fnRule (g : Γ(Xo.XF c, ⊤)) {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (fnRule g) y = fnAt (basePt y) g := by
  have h := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c S y
  unfold evR evalAt
  rw [dite_eq_left h, basePt_frMap h.choose_spec.choose_spec.choose_spec, fnAt_comp]
  rfl

end Rule

section Law

variable {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)

end Law

section Coefficients

open GlobalTheory.ShortDatumEq

variable {a : IsAuxiliarySplitSquarefreeLevel l}

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) {n : ℕ}

end Coefficients

theorem fnRule_injective : Function.Injective (fnRule (Xo := Xo) (c := c)) := by
  intro g g' h
  refine fn_ext fun z _ => ?_
  obtain ⟨p, j, y, ⟨hj, h1, h2⟩, z, rfl⟩ :=
    GlobalTheory.Frames.exists_openChart_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c z
  have e : basePt y = j := pullback.hom_ext (by rw [basePt, pullback.lift_fst, h1]) (by rw [basePt, pullback.lift_snd, h2])
  have e' : fnAt j g = fnAt j g' := e ▸ congrFun (congrFun h p) y
  have e'' : j.appTop.hom g = j.appTop.hom g' :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of p.R)).hom).1 e'
  refine (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1 ?_
  refine (gs_stalkMap j z ⊤ trivial g).symm.trans (Eq.trans ?_ (gs_stalkMap j z ⊤ trivial g'))
  rw [gs_eq j z ⊤ trivial, gs_eq j z ⊤ trivial]
  exact congrArg _ e''

section Datum

open GlobalTheory.ShortDatumEq

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (n : ℕ)

variable {n}

end Datum

end GlobalTheory.LevelCoverCompare
