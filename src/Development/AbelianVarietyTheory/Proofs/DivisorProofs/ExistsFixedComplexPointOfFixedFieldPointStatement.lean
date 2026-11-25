module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyRingHomComplexOfFg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
public import Mathlib.Algebra.FreeAlgebra.Cardinality
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPoint, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPointStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPoint =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPoint", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible\npublic import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues\npublic import Mathlib.Algebra.FreeAlgebra.Cardinality\npublic import Mathlib.Algebra.MvPolynomial.Cardinal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\npublic import Mathlib.FieldTheory.IsAlgClosed.Classification\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\npublic import Mathlib.RingTheory.Algebraic.Cardinality\nimport Mathlib.RingTheory.Henselian\npublic import Mathlib.RingTheory.Localization.Cardinality\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne\nimport Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero\nimport Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular\nimport Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart\nimport Formalism.LocalRingCardinality.DataTheta\nimport Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange\nimport Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf\nimport Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.FixedCx

open Cardinal

theorem mk_le_of_essFiniteType {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] :
    #S ≤ max #R ℵ₀ := by
  have h1 : #S ≤ #(Algebra.EssFiniteType.subalgebra R S) :=
    IsLocalization.cardinalMk_le (Algebra.EssFiniteType.submonoid R S)
  have h2 := Algebra.cardinalMk_adjoin_le R ((Algebra.EssFiniteType.finset R S : Finset S) : Set S)
  have h3 : #(((Algebra.EssFiniteType.finset R S : Finset S) : Set S)) ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite _).le
  refine h1.trans (h2.trans ?_)
  exact max_le (max_le (le_max_left _ _) (h3.trans (le_max_right _ _))) (le_max_right _ _)

theorem nonempty_ringHom_complex (K : Type) [Field K] [CharZero K] (h : #K ≤ 𝔠) : Nonempty (K →+* ℂ) := by
  apply _root_.GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_mk_le <;> assumption

theorem cancel_spec_field {K L : Type} [Field K] [Field L] (φ : L →+* K) {X : Scheme.{0}} (a b : Sp L ⟶ X)
    (h : spMap φ ≫ a = spMap φ ≫ b) : a = b := by
  obtain ⟨⟨p, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective a
  obtain ⟨⟨q, β⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  obtain ⟨e, he⟩ := GlobalTheory.SS.residue_embedding_unique _ _ h
  subst e
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at he
  have : α = β := by
    ext c
    exact φ.injective (congrArg (fun g => g.hom c) he)
  rw [this]

end GlobalTheory.FixedCx


open GlobalTheory.FixedCx Cardinal in
theorem GlobalTheory.FixedCx.exists_fixed_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : Type) [Field k] (x : Sp k ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X), x ≫ ρ = x → ∃ x' : Sp ℂ ⟶ Xo.X, x' ≫ ρ = x' := by
  intro E _ _ _ H Dw l Xo k _ x ρ hx
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Xo.X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  have hι : Xo.X.fromSpecResidueField p ≫ ρ = Xo.X.fromSpecResidueField p :=
    cancel_spec_field φ.hom _ _ (by rw [Category.assoc] at hx; exact hx)
  haveI := Xo.smooth
  haveI := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Xo.X.fromSpecResidueField p ≫ Xo.s)
  have hess := GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType Xo.s p ψ hψ
  letI : Algebra (KA l) (Xo.X.residueField p) := ψ.hom.toAlgebra
  haveI : Algebra.EssFiniteType (KA l) (Xo.X.residueField p) := hess
  haveI : CharZero (KA l) := charZero_of_injective_ringHom (algebraMap ℚ (KA l)).injective
  haveI : CharZero (Xo.X.residueField p) := charZero_of_injective_ringHom ψ.hom.injective
  have hK : #(KA l) ≤ 𝔠 := (Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le
  have hc : #(Xo.X.residueField p) ≤ 𝔠 :=
    mk_le_of_essFiniteType.trans (max_le hK Cardinal.aleph0_le_continuum)
  obtain ⟨j⟩ := nonempty_ringHom_complex (Xo.X.residueField p) hc
  exact ⟨Spec.map (CommRingCat.ofHom j) ≫ Xo.X.fromSpecResidueField p, by rw [Category.assoc, hι]⟩
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPoint =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPointStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPointStatement", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPoint\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne\nimport Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero\nimport Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular\nimport Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart\nimport Formalism.LocalRingCardinality.DataTheta\nimport Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange\nimport Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf\nimport Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPointStatement =====
