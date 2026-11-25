module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.LogKSChart

section Data

variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R)
  (gam : Fin m → LinearMap.BilinForm ℤ Q.X)

def constHom {k : Type} [Field k] (ρ : R →+* DualNumber k) : R →+* DualNumber k :=
  (algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)

def IsUnitPart (y : Q.X) (n : Fin m → ℕ)
    (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c y).left) fun _ => -1)) : Prop :=
  ψ₀.IsGen ∧ (∀ i, gam i y y = 2 * n i) ∧ ∃ e : (FractionRing R)ˣ,
    (e : FractionRing R) = algebraMap R _ (∏ i, t i ^ n i) ∧ ∀ z J, Good Q.P.L z J →
      val (Q.psi y) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn e) * val ψ₀ (toUnit (TK R)).left z J

end Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.LogKSChart
