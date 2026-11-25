module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem quasiCompact_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X : Scheme.{0}} (f : X ⟶ Sp V)
    (h₁ : QuasiCompact (pullback.snd f (spMap (IsLocalRing.residue V))))
    (h₂ : QuasiCompact (pullback.snd f (jK V))) : QuasiCompact f := by
  have c₁ : CompactSpace ↥(pullback f (spMap (IsLocalRing.residue V))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have c₂ : CompactSpace ↥(pullback f (jK V)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f _)
  have hu : Set.range (pullback.fst f (spMap (IsLocalRing.residue V))) ∪ Set.range (pullback.fst f (jK V)) =
      Set.univ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro x
    have hx : (Sp V).fromSpecResidueField (f x) (default : PrimeSpectrum _) = f x :=
      Scheme.fromSpecResidueField_apply _ _
    rcases ZJ.field_point_factor_dvr V ((Sp V).residueField (f x)) ((Sp V).fromSpecResidueField (f x)) with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
    · exact Or.inr ⟨r (default : PrimeSpectrum _), (congrArg (fun g => g (default : PrimeSpectrum _)) hr).symm.trans hx⟩
  have : CompactSpace X := ⟨hu ▸ (isCompact_range (pullback.fst f _).continuous).union
    (isCompact_range (pullback.fst f _).continuous)⟩
  exact (quasiCompact_iff_compactSpace f).2 this

theorem isSemiAbelian_of_unifPre_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], UnifPre (maximalIdeal V) D A G → IsSemiAbelian G := by
  intro V _ _ _ D A G _ _ U
  obtain ⟨E, -, -, -, -, hE⟩ := gtCoord_isGt V (maximalIdeal V) D.toPre 0 G ⟨U.gt 0⟩
  have h0 := isSemiAbelian_of_isGt _ E _ hE
  have := U.gen_hom
  have hK : IsSemiAbelian ((Over.pullback (jK V)).obj G) :=
    isSemiAbelian_of_grpIso U.gen (isSemiAbelian_of_isAbelianScheme A.A A.isAb)
  let ρ : V ⧸ (maximalIdeal V) ^ (0 + 1) →+* ResidueField V :=
    Ideal.Quotient.factor (Ideal.pow_le_self (by norm_num))
  have hr : spMap (residue V) = spMap ρ ≫ thick V (maximalIdeal V) 0 := by
    rw [← Spec.map_comp]
    congr 1
  have hk : IsSemiAbelian ((Over.pullback (spMap (residue V))).obj G) := by
    rw [hr]
    exact isSemiAbelian_of_grpIso (pullCompIso (spMap ρ) (thick V (maximalIdeal V) 0) G)
      (IsSemiAbelian.pullback (spMap ρ) _ h0)
  exact ZJ.isSemiAbelian_of_fibres_dvr V G U.smooth U.separated
    (quasiCompact_of_fibres_dvr V G.hom hk.quasiCompact hK.quasiCompact) hk hK

end GlobalTheory
