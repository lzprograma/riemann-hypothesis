module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def thirdDiff {A U : Type} [CommGroup A] [CommGroup U] (f : A → U) (x y w : A) : U :=
  f (x * y * w) * (f (x * y))⁻¹ * (f (x * w))⁻¹ * (f (y * w))⁻¹ * f x * f y * f w * (f 1)⁻¹

section Sym

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev symLB (L : LB G.left) : LB G.left :=
  LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]

variable {G}

def symV {L : LB G.left} (σ : LB.Gen (symLB G L)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (x : T ⟶ G) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) σ x.left z J

variable (G)

structure CubSym where

  L : RigLB G

  cub : CubicalStr G L

  sym : LB.Gen (symLB G L.L)
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L)
  sym_cub : ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
    ∀ x y w : T ⟶ G, cubV cub z J x⁻¹ y⁻¹ w⁻¹ = thirdDiff (symV sym z J) x y w * cubV cub z J x y w

variable {G}

end Sym

section Iso

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G']
  [GrpObj G] [IsCommMonObj G]

end Iso

section Triv

variable {S : Scheme.{0}} {H G : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj G] [IsCommMonObj G]

def trivV {i : H ⟶ G} {L : LB G.left} (σ : LB.Gen (L.pull i.left)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.ι) (t : T ⟶ H) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L) σ t.left z J

variable {B : Over S} [GrpObj B] [IsCommMonObj B]

end Triv

section Pairing

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
  (c : CubicalStr G L)

end Pairing

section Torus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

def charV (χ : X) {T : Over S} (z : T.left) (t : T ⟶ splitTorus S X) : (T.left.presheaf.stalk z)ˣ :=
  gm t.left z ⊤ (charUnit S X χ)

end Torus

section Examples

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
