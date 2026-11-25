module

public import Mathlib.RingTheory.Smooth.StandardSmooth
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieInh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}}

variable {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)

end GlobalTheory.CompanionTheory.Ar.LieInh

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

end GlobalTheory.CompanionTheory.Ar
