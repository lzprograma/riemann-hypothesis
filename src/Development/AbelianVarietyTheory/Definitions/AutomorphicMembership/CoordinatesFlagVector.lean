module

public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MulVecMemLatMap
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmStarOfIsCMUnram
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre, Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataSpaces\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.SA

open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat

def ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) : HermSpace E S.V where
  B := S.hT.flip
  herm x y := S.herm.eq y x
  nondeg x h := S.nondeg.2 x h

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}

abbrev latX (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := Λ ⊓ rs R F.X

def redLat (F : FlagD H r) (Λ : Submodule R V) : Submodule R V := (Λ ⊓ rs R (perp H F.X)) ⊔ rs R F.X

def IsPairMap (F F' F'' : FlagD H r) (Λ : Submodule R V) (g : R) (β : V ≃ₗ[K] V) : Prop :=
  F'.X.map (β : V →ₗ[K] V) = F''.X ∧ (perp H F'.X).map (β : V →ₗ[K] V) = perp H F''.X ∧
  (∀ x ∈ perp H F'.X, ∀ y ∈ perp H F'.X, H.B (β x) (β y) = H.B x y) ∧
  imLat β (redLat F' Λ) = redLat F'' Λ ∧ β F'.z - F''.z ∈ F''.X ∧
  ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), ∀ l'' ∈ Λ ⊓ rs R (perp H F''.X), β l' - l'' ∈ F''.X →
    l'' - l' ∈ latX F Λ ⊔ smulLat g Λ



namespace FlagExample

open NumberField Formalism.BasicNotions.Examples₂

variable (E : Type) [Field E] [NumberField E] [StarRing E]

variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)

end FlagExample

end GlobalTheory.SA

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataSpaces\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MulVecMemLatMap\nimport Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer\nimport Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmStarOfIsCMUnram\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice\nimport Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FractionFieldToGenericStalkAlgebraMapEq\npublic import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre\nimport Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.IntPair

open NumberField Matrix Formalism.BasicNotions Formalism.HermitianLatticeCounting.S6 GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntTerm GlobalTheory.SA
open GlobalTheory.HermLat (perp rs smulLat imLat isomGrp mem_isomGrp IsUnimod)

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r g : ℕ}

def co (x : S.V) : Fin S.rank → E := S.frame.equivFun x

variable {S} {T T' : E} {A : Matrix (Fin S.rank) (Fin (r + 1)) E} {Λ Λ₁ : Submodule (𝓞 E) (Fin S.rank → E)}
  {s t : S.V ≃ₗ[E] S.V} {F F' G : FlagD (ofHSpace S) r}

end GlobalTheory.IntPair

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector =====
