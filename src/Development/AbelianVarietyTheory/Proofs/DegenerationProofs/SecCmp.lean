module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PsiRing

def FibNZ {Y S : Scheme.{0}} (p : Y ⟶ S) {M : LB Y} (s : LB.Sec M) : Prop :=
  ∀ y : S, ∃ z : Y, p z = y ∧ z ∈ nonzeroLocus s

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def Mult (D : DegPre R) (th g : SecBT D (𝟙_ _) 1 0) (b : R) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval g r z J = cst (r ≫ (𝟙_ _ ⊗ D.P.A).hom) z b * sval th r z J

def Coef (D : DegPre R) (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (th : SecBT D (𝟙_ _) 1 0) (g : SecBT D (𝟙_ _) 1 χ) (b : R) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
    sval g (lift (toUnit T) y).left z J = cst T.hom z b * ((val u (toUnit T).left z J * rigV D z J).val *
      sval th (lift (toUnit T) (y * cT D T χ)).left z J)

def SecCmp (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β))
    (xe : D'.X ≃+ D.X) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α) : Prop :=
  ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
    r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' →
      sval (f (xe α)) r z J = (∏ i : Fin 4, gw v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ β))
        (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε 1 i).val * sval (f' α) r' z J'

abbrev RigCmp (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left)
    (v : LB.Iso D'.P.L (D.P.L.pull β)) : Prop :=
  PMaps v (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ)

abbrev PsiCmp (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β))
    (xe : D'.X ≃+ D.X) (gam : (TK V).left ⟶ (TK R).left) : Prop :=
  ∀ x, PMaps v (K := PUnit) (fun _ => D'.xK x) (fun _ => D.xK (xe x)) (fun _ => -1) (D'.psi x) (D.psi (xe x)) gam

end GlobalTheory.PsiRing
end
