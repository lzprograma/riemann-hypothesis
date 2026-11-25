module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers, Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond

-- ===== clump member: Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot\npublic import Formalism.LocalToGlobal.ProjectiveLattices.ThClass\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing\npublic import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity\npublic import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace\npublic import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis\npublic import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot
open scoped TensorProduct

section Lattices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {r n : ℕ}

def barI (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)

def InLevel (r M : ℕ) (PQ : Ideal (𝓞 E)) (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  (γ.map cc).transpose * γ = 1 ∧ OneMod M γ ∧
    ∃ k : ℕ, Nat.Coprime k (Ideal.absNorm PQ) ∧ ∀ i b : Fin n, r ≤ i.val → b.val < r →
      ∃ o ∈ PQ, (k : E) * γ i b = ((o : 𝓞 E) : E)

def Carries (γ : Matrix (Fin n) (Fin n) E) (L L' : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v, v ∈ L' ↔ ∃ u ∈ L, v = γ.mulVec u

end Lattices

section Record

variable {D : D7}

abbrev IdF (D : D7) : Type := (AdE D.host.F D.host.E)ˣ

variable (T : CoreJ D) {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ)

variable {T} {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)

variable (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
  (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) (β : Fin D.R.r → (T.Q.Dw j).La)
  (Cl : D.what₂.Tup → Type) [∀ t, Fintype (Cl t)]
  (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : D.what₂.Tup → c'.F)
  (thAd : ∀ t, (Cl t → VVc c' lam) → AutQ (T.V j (sig0 T.Q.c)) → ℂ) (Pl : ∀ t, (Cl t → VVc c' lam) → Prop) (ph : ℂ)
  (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ)
  (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
  (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
  (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
  (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
  (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F)

end Record

end GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers\npublic import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot\npublic import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing\npublic import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge\n\n"}
section -- clump:auto
@[expose] public section


set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.ClassTieCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
open Formalism.L2.PjFree (Unf.ofPj)
open scoped TensorProduct Matrix

section Scalar

variable {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ}

def IsDetOf (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)) : Prop :=
  𝔠 ⊔ barI H 𝔠 = ⊤ ∧ Submodule.span (𝓞 D.host.E) (detSet L) * idlE (barI H 𝔠) = idlE 𝔠

def SquareLaw (n bad r : ℕ) : Prop :=
  ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)), GlobalTheory.ClassScalarCompare.Guard H bad L →
    IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm 𝔠 : ℚ)

variable {H} {Dw : Datum H} {l : Level H} {c : Coeff l}

theorem isDetOf_unique {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a b : Ideal (𝓞 D.host.E)} (ha : IsDetOf H L a)
    (hb : IsDetOf H L b) : a = b := by
  have e : idlE (a * barI H b) = idlE (b * barI H a) := by
    have m : ∀ I J : Ideal (𝓞 D.host.E), idlE (I * J) = idlE I * idlE J := fun I J =>
      Submodule.map_mul I J (Algebra.ofId (𝓞 D.host.E) D.host.E)
    rw [m, m, ← ha.2]
    conv_rhs => rw [← hb.2]
    ring
  have e' : a * barI H b = b * barI H a :=
    Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 D.host.E) D.host.E)
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) e
  exact le_antisymm
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 hb.1).dvd_of_dvd_mul_right ⟨_, e'⟩))
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 ha.1).dvd_of_dvd_mul_right ⟨_, e'.symm⟩))

theorem exists_epIs_iff (bad : ℕ) (B : Ideal (𝓞 D.host.E) → c.F) :
    (∃ epF : Submodule (𝓞 D.host.E) (Fin n → D.host.E) → c.F, EpIs (Dw := Dw) c bad B epF) ↔
      SquareLaw H n bad (Dw.p + Dw.q) := by
  classical
  constructor
  · rintro ⟨epF, h⟩ L 𝔠 g h1
    obtain ⟨q, q0, q1, -⟩ := h L 𝔠 g.1 g.2.1 g.2.2 h1.1 h1.2
    exact ⟨q, q0, q1⟩
  · intro h
    have key : ∀ L : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∃ v : c.F, ∀ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L →
        IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
          q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
            (Ideal.absNorm 𝔠 : ℚ) ∧ v = (B 𝔠)⁻¹ * (q : c.F) := by
      intro L
      by_cases hL : ∃ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L ∧ IsDetOf H L 𝔠
      · obtain ⟨𝔠, g, h1⟩ := hL
        obtain ⟨q, q0, q1⟩ := h L 𝔠 g h1
        refine ⟨(B 𝔠)⁻¹ * (q : c.F), fun 𝔠' _ h2 => ?_⟩
        obtain rfl := isDetOf_unique h1 h2
        exact ⟨q, q0, q1, rfl⟩
      · exact ⟨0, fun 𝔠 g h1 => absurd ⟨𝔠, g, h1⟩ hL⟩
    choose epF hepF using key
    exact ⟨epF, fun L 𝔠 g1 g2 g3 h1 h2 => hepF L 𝔠 ⟨g1, g2, g3⟩ ⟨h1, h2⟩⟩

end Scalar

end GlobalTheory.ClassTieCompare
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond =====
