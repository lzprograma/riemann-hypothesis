module

public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical

namespace GlobalTheory.TorRef

section Branches

variable {X X' : Scheme.{0}}

def pre (π : X' ⟶ X) (Z : Closeds X) : Closeds X' := Z.preimage π.continuous

abbrev van (Z : Closeds X) (x : X) : Ideal (X.presheaf.stalk x) :=
  FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x

def tr {x y : X} (h : x = y) : X.presheaf.stalk x →+* X.presheaf.stalk y :=
  (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom

def IsRsp {A : Type} [CommRing A] [IsLocalRing A] {ι : Type} [Fintype ι] (f : ι → A) : Prop :=
  IsRegularLocalRing A ∧ Ideal.span (Set.range f) = maximalIdeal A ∧ (Fintype.card ι : WithBot ℕ∞) = ringKrullDim A

def BrAt (B : Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x) : Prop :=
  IsRsp f ∧ van B x = Ideal.span {∏ j, f (Sum.inl j)}

def ColAt (B : Closeds X) {ι : Type} (E : ι → Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x)
    (c : Fin m → ι) : Prop :=
  BrAt B x f ∧ ∀ i, van (E i) x = Ideal.span {∏ j ∈ Finset.univ.filter (fun j => c j = i), f (Sum.inl j)}

def IsStrict (B : Closeds X) {ι : Type} (E : ι → Closeds X) : Prop :=
  ∀ x : X, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (c : Fin m → ι), ColAt B E x f c ∧ Function.Injective c

end Branches

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsCN (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R ∧ CharZero R

abbrev toBase {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') : Over.mk (spMap φ) ⟶ Over.mk (𝟙 (Sp R)) :=
  Over.homMk (spMap φ) (Category.comp_id _)

end Sections

section Steps

def HomExtNormalSt : Prop :=
  ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), Geo.Tor.IsNormalScheme X → IsOpenImmersion j → IsDominant j →
    ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
    ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f

def PullSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R') (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → IsCN R' → Function.Injective φ → IsLocalHom φ → P.TorsionIso →
    ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap φ)) (P' : PELUnif (maximalIdeal R') t')
      (e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X), P'.TorsionIso ∧
      ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : R'ˣ, PsiCoord P'.D.toPre y (u * φ r)

end Steps

end GlobalTheory.TorRef
