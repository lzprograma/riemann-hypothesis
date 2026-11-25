module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Relabel

def TwJ {O : Type} [CommRing O] {N N' : NumD O} {k : ℕ} (β : N.Form k) (u r : Oˣ) (J : NumD.Iso (N.twist β u) N')
    {j : ℕ} (q : N.QT j) (q' : N'.QT j) : Prop :=
  ∃ p : (N.twist β u).QT j, TwRel β u r q p ∧ q'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q'.1.2
section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} {O : Type} [CommRing O] [StarRing O]

def actV (ν : NumOf D F N) (oa : D.P.OAct O) (x : O) (b : N.A) : N.A := ν.eA.symm (ν.eA b ≫ oa.act x)

def RosV (ν : NumOf D F N) (oa : D.P.OAct O) (x : O) (ρ : N.A → N.A → F) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.act (star x)) (oa.act x)) rosatiε), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) ∧
    ∀ b b', ρ b b' = vF u (lift (ν.eA b) (ν.eA b')).left ν.J

def ActCompat [Module O D.X] (ν : NumOf D F N) (oa : D.OAct O) {R' : Type} [CommRing R'] [IsDomain R'] {D' : DegPre R'}
    [Algebra (FractionRing R') F] {N' : NumD F} [Module O D'.X] (ν' : NumOf D' F N') (oa' : D'.OAct O) {k : ℕ}
    (β : N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (N.twist β u) N') : Prop :=
  ∀ j, 0 < j → ∀ (x : O) (p₀ p₁ : QkPt D F j) (p₀' p₁' : QkPt D' F j) q₀ q₁ q₀' q₁', QkAct oa x p₀ p₁ → ν.QPt p₀ q₀ →
    ν.QPt p₁ q₁ → TwJ β u (r j) J q₀ q₀' → TwJ β u (r j) J q₁ q₁' → ν'.QPt p₀' q₀' → ν'.QPt p₁' q₁' →
    QkAct oa' x p₀' p₁'
end
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {K : Type} [Field K]

abbrev FullI (o : Full D K) : Type :=
  letI := H.starRing
  TateIso D K (baseOver (Sp K) ⟶ o.P.A) (fun a g => g ≫ o.oa.act a) (fun n g g' c => WeilIs o.P.A o.P.L n g g' (unitOn c))

def withI (o : Full D K) (I : FullI o) : Full D K := { o with I := I }

end GlobalTheory.Relabel
end
