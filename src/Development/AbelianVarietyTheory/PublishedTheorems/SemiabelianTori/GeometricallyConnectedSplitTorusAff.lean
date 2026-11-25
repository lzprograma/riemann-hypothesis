module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

/-- **Extension of homomorphisms of semi-abelian schemes.** Let `S` be a noetherian scheme
whose local rings are integrally closed domains, and let `U ⊆ S` be a dense open subscheme.
If `G` and `H` are semi-abelian schemes over `S` (`IsSemiAbelian`), every homomorphism of group
schemes `G_U → H_U` over `U` extends uniquely to a homomorphism `G → H` over `S`. -/
def SemiAbelianHomExtension : Prop :=
  ∀ (S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S →
    ∀ (U : S.Opens), Dense (U : Set S) →
    ∀ (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H →
    ∀ f : (Over.pullback U.ι).obj G ⟶ (Over.pullback U.ι).obj H, IsMonHom f →
      ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback U.ι).map F = f

namespace SemiAbelianHomExtension

open ExtUnique

variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]

theorem quasiCompact_and_dominant (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (j : U ⟶ S) [IsOpenImmersion j]
    [IsDominant j] : QuasiCompact j ∧ IsSchemeTheoreticallyDominant j :=
  have := GlobalTheory.IsNormalScheme.of_pred hS
  dense_openImmersion j

theorem of_isGrpPullback (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over U} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ)
    (f : G' ⟶ H') [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, -⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨-, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  let V : S.Opens := j.opensRange
  have hV : Dense (V : Set S) := j.denseRange
  let e : V.toScheme ⟶ U := j.isoOpensRange.inv
  have he : e ≫ j = V.ι := j.isoOpensRange_inv_comp
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G V.ι)
    (((isGrpPullback_pullback G' e).comp hφ).congr he rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (((isGrpPullback_pullback H' e).comp hψ).congr he rfl)
    (isGrpPullback_pullback H V.ι)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := h S hS V hV G H hG hH (a.hom ≫ (Over.pullback e).map f ≫ b.hom) inferInstance
  have key : f.left ≫ ψ = φ ≫ F.left := by
    have h₁ := pullback_map_left_fst V.ι F
    rw [hF', Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc,
      ← Category.assoc ((Over.pullback e).map f).left, pullback_map_left_fst, Category.assoc,
      Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi (pullback.fst G'.hom e)).1 ((cancel_epi a.hom.left).1 h₁)
  exact ⟨F, ⟨hF, key⟩, fun F' hF' => ExtUnique.over_hom_ext_of_isPullback hφ.1 (hF'.2.symm.trans key)⟩

theorem existsUnique_oAct_of_isGrpPullback (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j]
    {G : Over S} [GrpObj G] (hG : IsSemiAbelian G) {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hφ : IsGrpPullback G' G j φ) {O : Type} [CommRing O] (i : OAct O G') :
    ∃! a : OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  refine ExtUnique.existsUnique_oAct_of_isGrpPullback hφ i fun x => ?_
  have := i.hom x
  obtain ⟨F, ⟨-, hF⟩, -⟩ := h.of_isGrpPullback hS hG hG hφ hφ (i.act x)
  exact ⟨F, hF⟩

theorem existsUnique_iso_of_isGrpPullback (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j]
    {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over U}
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ)
    (hψ : IsGrpPullback H' H j ψ) (e : G' ≅ H') [IsMonHom e.hom] :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ e.hom.left ≫ ψ = φ ≫ E.hom.left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨F, ⟨hF, hF'⟩, hu⟩ := h.of_isGrpPullback hS hG hH hφ hψ e.hom
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := h.of_isGrpPullback hS hH hG hψ hφ e.inv
  obtain ⟨h₁, h₂⟩ := ExtUnique.comp_eq_id_of_isPullback hφ.1 hψ.1 e F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, ⟨hF, hF'⟩, fun E hE => Iso.ext (hu E.hom hE)⟩

theorem existsUnique_iso_of_extensions (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j]
    {A : Over U} [GrpObj A] {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ H.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A H j ψ) :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ φ ≫ E.hom.left = ψ := by
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  simpa [eq_comm] using h.existsUnique_iso_of_isGrpPullback hS hG hH hφ hψ (Iso.refl A)


section Dvr

variable (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
  [IsFractionRing T K]

theorem isNormalScheme_dvr : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp T) :=
  GlobalTheory.IsNormalScheme.pred _

variable {T K}

end Dvr

end SemiAbelianHomExtension

end GlobalTheory.Published
