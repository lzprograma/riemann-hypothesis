module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.Divisors.NotHasNonzeroSecOfIsEmpty, Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Divisors.NotHasNonzeroSecOfIsEmpty =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Divisors.NotHasNonzeroSecOfIsEmpty", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.PositivityModel

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H L N A : LB X}

section Space
open ProjSpace
variable (k) (D : ℕ)

end Space

end GlobalTheory.PositivityModel
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Divisors.NotHasNonzeroSecOfIsEmpty =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere\npublic import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.NotHasNonzeroSecOfIsEmpty\nimport Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace\nimport Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Adelic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.QCoh

namespace GlobalTheory.ProjVar

namespace Var

variable {F : Type} [Field F] (Y : Var F)

instance isNoetherian_X : AlgebraicGeometry.IsNoetherian Y.X :=
  isNoetherian_of_isProjOver Y.isProjOver

def sheaf (Δ : Y.Dv) : Y.X.Modules := twist (structureModule Y.X) (Y.lb Δ)

abbrev H (i : ℕ) (Δ : Y.Dv) : Type := coh (Y.sheaf Δ) i

def hdim (i : ℕ) (Δ : Y.Dv) : ℕ := GlobalTheory.hdim F (Y.sheaf Δ) i

def chi (Δ : Y.Dv) : ℤ := GlobalTheory.chi F (Y.sheaf Δ)

def hZeroEquiv (Δ : Y.Dv) : Y.H 0 Δ ≃ₗ[F] Y.H0 Δ := cohEquiv (presents_toLB Δ)


variable {Y} in
theorem hdim_eq_of_toPic_eq {Δ : Y.Dv} {L : LB Y.X} (hL : L.IsLB) (e : toPic Δ = cls L hL) (i : ℕ) :
    Y.hdim i Δ = GlobalTheory.hdim F (twist (structureModule Y.X) L) i :=
  (nonempty_twist_iso_of_cls_eq _ (isLB_toLB Δ) hL e).elim (hdim_congr F i)


variable {Y} in
theorem hdim_congr {Δ Δ' : Y.Dv} (e : toPic Δ = toPic Δ') (i : ℕ) : Y.hdim i Δ = Y.hdim i Δ' :=
  hdim_eq_of_toPic_eq (isLB_toLB Δ') e i

def inter (Δ : Fin Y.dim → Y.Dv) : ℤ := interNum F (structureModule Y.X) fun i => Y.lb (Δ i)

theorem inter_eq_multiDiff (Δ : Fin Y.dim → Y.Dv) : Y.inter Δ = multiDiff Δ Y.chi 0 := by
  have e := congrFun (multiDiff_comap toPic Δ (chiPic F (structureModule Y.X))) 0
  rw [Function.comp_apply, map_zero] at e
  exact (interNum_eq_multiDiff F _ fun i => isLB_toLB (Δ i)).trans e.symm


variable {Y} in
theorem inter_eq_of_toPic_eq {Δ : Fin Y.dim → Y.Dv} {L : Fin Y.dim → LB Y.X}
    (hL : ∀ i, (L i).IsLB) (e : ∀ i, toPic (Δ i) = cls (L i) (hL i)) :
    Y.inter Δ = interNum F (structureModule Y.X) L :=
  interNum_congr_cls F _ (fun i => isLB_toLB (Δ i)) hL e


theorem inter_comp_perm (Δ : Fin Y.dim → Y.Dv) (σ : Equiv.Perm (Fin Y.dim)) :
    Y.inter (Δ ∘ σ) = Y.inter Δ :=
  interNum_comp_perm F _ (L := fun i => Y.lb (Δ i)) (fun i => isLB_toLB (Δ i)) σ

theorem inter_const (Δ : Y.Dv) : Y.inter (fun _ => Δ) = topSelfIntersection F (Y.lb Δ) Y.dim := rfl

theorem diffVanish_chi : DiffVanish (Y.dim + 1) Y.chi :=
  (diffVanish_chiPic_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver
    (by rw [suppDim_structureModule, Y.topologicalKrullDim_eq])).comap toPic

def interForm : MultilinearMap (RingHom.id ℤ) (fun _ : Fin Y.dim => Y.Dv) ℤ := Y.diffVanish_chi.form

@[simp] theorem interForm_apply (Δ : Fin Y.dim → Y.Dv) : Y.interForm Δ = Y.inter Δ :=
  (Y.diffVanish_chi.form_apply Δ 0).trans (Y.inter_eq_multiDiff Δ).symm

theorem inter_zsmul (n : Fin Y.dim → ℤ) (Δ : Fin Y.dim → Y.Dv) :
    Y.inter (fun i => n i • Δ i) = (∏ i, n i) * Y.inter Δ := by
  simp only [← interForm_apply, MultilinearMap.map_smul_univ, RingHom.id_apply, smul_eq_mul]

def IsCurve (Z : Y.Cl) : Prop :=
  IsIrreducible (Z : Set Y.X) ∧ topologicalKrullDim (Z : Set Y.X) = 1

def deg (C : Y.Cl) (Δ : Y.Dv) : ℤ := interNumRed F C ![Y.lb Δ]






theorem isCurve_iff (Z : Y.Cl) : Y.IsCurve Z ↔ IsCompleteCurve F Z := (Y.isCompleteCurve_iff Z).symm


variable {Y}

theorem deg_principal (C : Y.Cl) (g : Y.Fnˣ) : Y.deg C (principal g) = 0 :=
  interNumRed_one_eq_zero (isLB_toLB _) (toPic_principal g) C

@[simp] theorem deg_zero (C : Y.Cl) : Y.deg C 0 = 0 := deg_principal C 1

namespace IsCurve

variable {C : Y.Cl} (hC : Y.IsCurve C)

include hC

theorem deg_add (A B : Y.Dv) : Y.deg C (A + B) = Y.deg C A + Y.deg C B :=
  ((Y.isCurve_iff C).1 hC).interNumRed_of_cls_eq_add Y.isAmple_projective_O_one (isLB_toLB _) (isLB_toLB A)
    (isLB_toLB B) (map_add toPic A B)

def degHom : Y.Dv →+ ℤ := AddMonoidHom.mk' (Y.deg C) hC.deg_add

end IsCurve


variable (Y) in
def nef (Δ : Y.Dv) : Prop := IsNef F (Y.lb Δ)


variable (Y) in
def big (Δ : Y.Dv) : Prop := IsBig F (Y.lb Δ)


variable (Y) in
def ample (Δ : Y.Dv) : Prop := IsAmpleLB (Y.lb Δ)

variable {Δ A B : Y.Dv} {L : LB Y.X}



theorem hasNonzeroSec_iff : HasNonzeroSec (Y.lb Δ) ↔ Y.H0 Δ ≠ ⊥ :=
  hasNonzeroSec_iff_nontrivial.trans
    ((Y.hZeroEquiv Δ).toEquiv.nontrivial_congr.trans Submodule.nontrivial_iff_ne_bot)

end Var

section Proj

open ProjSpace

variable (F : Type) [Field F] (n : ℕ)

end Proj

end GlobalTheory.ProjVar
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane =====
