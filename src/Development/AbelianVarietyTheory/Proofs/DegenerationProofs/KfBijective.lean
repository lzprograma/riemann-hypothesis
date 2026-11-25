module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.ClassWeight
open GlobalTheory.UT

def kf (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    F →+* Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem kf_bijective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Bijective (kf R F) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem base_eq : (show (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left from spMap y₀) ≫
    (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
  refine (Category.comp_id _).trans ?_
  exact (congrArg spMap u.fac.symm).trans
    (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p))))

def Moved (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)) {k : ℕ} (t : SecA u.A (PadicAlgCl p) k)
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : Prop :=
  ThetaPtMove.SecRel u.cart (T := TFK (R := u.V) (PadicAlgCl p)) (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) w t s

theorem exists_moved {w : LB.Iso u.A.L (ρ.P.L.pull u.φ)} (hw : w.IsGen) {k : ℕ}
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : ∃ t, Moved u w t s :=
  ThetaPtMove.exists_secRel u.cart _ _ hw ρ.P.isLB u.A.isLB s

end GlobalTheory.ZH.ClassWeight
end
