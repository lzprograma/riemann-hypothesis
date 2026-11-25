module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

noncomputable section

namespace GlobalTheory.ModelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ObjPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Obj

variable {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {f : S' ⟶ S}

def objOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : Obj D l b (f ≫ s) :=
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  { t := t'
    proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
    ample := hp.2.1 o.ample
    ktriv := hp.2.2 o.ktriv
    eta := fun a => secPull m.cart (o.eta a)
    eta_add := fun a c => by rw [o.eta_add, map_mul]
    eta_ker := fun a ha => by rw [o.eta_ker a ha, map_one]
    etaA := fun a => secPull m.cart (o.etaA a)
    etaA_add := fun a c => by rw [o.etaA_add, map_mul]
    etaA_ker := fun a => by rw [o.etaA_ker a, map_one]
    geom := fun k _ _ x β hx => by
      obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
      refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I,
        hI, fun a => ?_, fun a ha => ?_⟩
      · rw [GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ,
          GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ]
        exact hdet τ
      · apply Over.OverMorphism.ext
        show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
        rw [Category.assoc, m.act, Category.assoc]
      · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
          m.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hA a))
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hM a ha)) }

def objMapOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : ObjMap (objOfSABMap o m) o f :=
  ⟨m, fun _ => secPull_left m.cart _, fun _ => secPull_left m.cart _⟩

theorem sec_eq_secPull {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) {e : 𝟙_ (Over S) ⟶ t.G}
    {e' : 𝟙_ (Over S') ⟶ t'.G} (h : e'.left ≫ m.φ = f ≫ e.left) : e' = secPull m.cart e := by
  apply Over.OverMorphism.ext
  apply m.cart.1.hom_ext
  · exact h.trans (secPull_left m.cart _).symm
  · rw [Over.w, Over.w]

end Obj

end GlobalTheory.ModelCompare
