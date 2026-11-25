module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.NNReal.Defs

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def HomExtDvrSt : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (G G' : Over (Spec (CommRingCat.of T))) [GrpObj G] [GrpObj G'],
    IsSemiAbelian G → IsSemiAbelian G' →
    ∀ φ : genFibre T G ⟶ genFibre T G', IsMonHom φ →
      ∃! ψ : G ⟶ G', IsMonHom ψ ∧ (Over.pullback (specMap T (FractionRing T))).map ψ = φ

structure Laws7 : Prop where
  homExtDvr : HomExtDvrSt

end ReciprocityTheory.ChartRestriction.G.Out
