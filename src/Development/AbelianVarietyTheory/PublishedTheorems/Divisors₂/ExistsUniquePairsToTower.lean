module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DeRhamVectorExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
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

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent unitOn)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta)
open ReciprocityTheory.ChartRestriction.G.Out (WeilIs)
open GlobalTheory.Cris (dp0)
open GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace EpsWeil

variable {R : Type} [CommRing R] (D : Type) [CommRing D] [Algebra R D]


variable {D} in
def epsUnit (b : D) : (DualNumber D)ˣ where
  val := 1 + TrivSqZeroExt.inr b
  inv := 1 - TrivSqZeroExt.inr b
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp


variable (R) in
def epsMap : DualNumber R →ₐ[R] DualNumber D :=
  DualNumber.lift ⟨(Algebra.ofId R _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ ↦ Commute.all _ _⟩

variable {D} {A B : Over (Sp R)} [GrpObj A] [GrpObj B]
theorem unitOn_bijective : Function.Bijective (unitOn (R := D)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of D)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem map_unitOn {D' : Type} [CommRing D'] (f : D →+* D') (u : Dˣ) :
    Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map f.toMonoidHom u) :=
  Units.ext (congrArg (fun q ↦ q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

end EpsWeil

namespace Published

namespace BarsottiTateDieudonne

def WittModule : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p],
    ∃ (M : PDivGroup p k → ModuleCat.{0} (WittVector p k))
      (map : ∀ G H : PDivGroup p k, (G ⟶ H) →+ (M H →ₗ[WittVector p k] M G))
      (red : ∀ G : PDivGroup p k,
        M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt),
      (∀ G : PDivGroup p k, Module.Free (WittVector p k) (M G) ∧ Module.Finite (WittVector p k) (M G) ∧
        Module.finrank (WittVector p k) (M G) = G.height ∧ Function.Surjective (red G) ∧
        (∀ m, red G m = 0 ↔ ∃ n, m = p • n) ∧ map G G (𝟙 G) = LinearMap.id) ∧
      (∀ (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K),
        map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
      ∀ (G H : PDivGroup p k) (f : G ⟶ H) (m : M H),
        red G (map G H f m) = PDivGroup.rigExtMap f (red H m)

end BarsottiTateDieudonne

end Published

end GlobalTheory
