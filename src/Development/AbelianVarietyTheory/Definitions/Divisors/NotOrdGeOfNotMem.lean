module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {F : SFam g n ζ}

def OrdGe (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def OrdEq (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

variable {M}

variable (M)

end Ord

def TraitExtSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (T : Trait F) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧
        f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

end GlobalTheory.Poinc
