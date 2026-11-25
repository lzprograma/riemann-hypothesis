module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddings, Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddingsStatement

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddings =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddings", "h": "module\n\npublic import Mathlib.LinearAlgebra.Charpoly.Basic\npublic import Mathlib.NumberTheory.NumberField.Basic\npublic import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.LinearAlgebra.Charpoly.ToMatrix\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Polynomial NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem map_charpoly_lmul_eq_prod_embeddings (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [Fintype (E →+* Ω)]
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E) (a : 𝓞 E) :
    (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom Ω) =
      ∏ s : E →+* Ω, (X - C (s (a : E))) := by
  classical
  let e := NumberField.RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* Ω) := by
    rw [← Module.finrank_eq_card_basis e, NumberField.RingOfIntegers.rank, ← hc,
      Nat.card_eq_fintype_card]
  let eqv := Fintype.equivOfCardEq hcard
  let P : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E →ₐ[ℤ] Ω :=
    fun j => ((eqv j).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  have hP : Function.Injective P := by
    intro i j hij
    apply eqv.injective
    apply IsFractionRing.injective_comp_algebraMap (A := 𝓞 E) (K := E) (L := Ω)
    show (eqv i).comp (algebraMap (𝓞 E) E) = (eqv j).comp (algebraMap (𝓞 E) E)
    ext x
    exact DFunLike.congr_fun hij x
  have h := GlobalTheory.map_charpoly_leftMulMatrix_eq_prod_algHom e hP a
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, algebraMap_int_eq] at h
  refine h.trans ?_
  exact Fintype.prod_equiv eqv _ _ fun j => rfl

theorem charpoly_lmul_splits_of_conjugates (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [CharZero Ω] (O : Type) [CommRing O] [Algebra O Ω]
    (K : Type) [Field K] (g : O →+* K) (hinj : Function.Injective (algebraMap O Ω))
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E)
    (hO : ∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) (a : 𝓞 E) :
    ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits := by
  classical
  haveI : Finite (E →+* Ω) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* Ω) := Fintype.ofFinite _
  have hO' : ∀ (s' : E →+* Ω) (a : 𝓞 E), ∃ y, algebraMap O Ω y = s' (a : E) :=
    fun s' a => RingHom.mem_range.mp (hO s' a)
  choose o ho using hO'
  have hΩ := GlobalTheory.CompanionTheory.Ar.Flat.DegZ.map_charpoly_lmul_eq_prod_embeddings E Ω hc a
  have hO2 : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom O) =
      ∏ s : E →+* Ω, (X - C (o s a)) := by
    apply Polynomial.map_injective (algebraMap O Ω) hinj
    rw [Polynomial.map_map,
      RingHom.ext_int ((algebraMap O Ω).comp (Int.castRingHom O)) (Int.castRingHom Ω), hΩ,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ho]
  have hK : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K) =
      ∏ s : E →+* Ω, (X - C (g (o s a))) := by
    rw [RingHom.ext_int (Int.castRingHom K) (g.comp (Int.castRingHom O)), ← Polynomial.map_map, hO2,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hK]
  exact Polynomial.Splits.prod fun s _ => Polynomial.Splits.X_sub_C _

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddings =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddingsStatement =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddingsStatement", "h": "module\n\npublic import Mathlib.LinearAlgebra.Charpoly.Basic\npublic import Mathlib.NumberTheory.NumberField.Basic\npublic import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddings\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\npublic import Mathlib.CategoryTheory.Monoidal.Cartesian.Over\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes\nimport Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft\nimport Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars\nimport Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne\nimport Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW\nimport Mathlib.Topology.Sheaves.Presheaf\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem _root_.GlobalTheory.T.charpoly_splits_of_embeddings : ∀ (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] [CharZero Ω] (O : Type) [CommRing O] [Algebra O Ω] (K : Type) [Field K] (g : O →+* K), Function.Injective (algebraMap O Ω) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → ∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.charpoly_lmul_splits_of_conjugates
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddingsStatement =====
