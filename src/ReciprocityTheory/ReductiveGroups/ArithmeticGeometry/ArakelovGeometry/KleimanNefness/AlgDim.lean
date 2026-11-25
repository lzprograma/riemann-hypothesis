module

import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionComponents
public import Mathlib.Data.ENat.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimSt
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.CommutativeAlgebra.SaturatedChains.DimFormulaOfSurjective, ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimA, ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim

-- ===== clump member: ReciprocityTheory.CommutativeAlgebra.SaturatedChains.DimFormulaOfSurjective =====
-- clump-header: {"m": "ReciprocityTheory.CommutativeAlgebra.SaturatedChains.DimFormulaOfSurjective", "h": "module\n\npublic import Mathlib.Data.ENat.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.CA

open IsLocalRing

theorem dimFormula_arith (a b : ℕ∞) (c d : WithBot ℕ∞) (n : ℕ) (hc : c ≠ ⊥) (hd : d ≠ ⊥)
    (h1 : ((a + b : ℕ∞) : WithBot ℕ∞) + c = n) (h2 : (a : WithBot ℕ∞) + d = n) :
    (b : WithBot ℕ∞) + c = d := by
  obtain ⟨c, rfl⟩ := WithBot.ne_bot_iff_exists.mp hc
  obtain ⟨d, rfl⟩ := WithBot.ne_bot_iff_exists.mp hd
  have e1 : a + b + c = (n : ℕ∞) := by exact_mod_cast h1
  have e2 : a + d = (n : ℕ∞) := by exact_mod_cast h2
  suffices e3 : b + c = d by exact_mod_cast e3
  induction a using ENat.recTopCoe with
  | top => simp at e2
  | coe a =>
    induction d using ENat.recTopCoe with
    | top => simp at e2
    | coe d =>
      induction b using ENat.recTopCoe with
      | top => simp at e1
      | coe b =>
        induction c using ENat.recTopCoe with
        | top => simp at e1
        | coe c =>
          norm_cast at e1 e2 ⊢
          omega

end ReciprocityTheory.CA
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.CommutativeAlgebra.SaturatedChains.DimFormulaOfSurjective =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimA =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimA", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimSt\npublic import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\npublic import Mathlib.RingTheory.Ideal.KrullsHeightTheorem\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge\npublic import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim\npublic import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField\nimport ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM\npublic import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.DimFormulaOfSurjective\npublic import Mathlib.RingTheory.Ideal.Height\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal

open ReciprocityTheory.CA

theorem ringKrullDim_quotient_ne_bot {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ringKrullDim (R ⧸ I) ≠ ⊥ := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial

theorem isCM_atPrime_of_le {S : Type*} [CommRing S] (𝔐 W : Ideal S) [𝔐.IsPrime] [W.IsPrime]
    (h : IsCM (Localization.AtPrime 𝔐)) (hle : W ≤ 𝔐) : IsCM (Localization.AtPrime W) := by
  have hdisj : Disjoint (𝔐.primeCompl : Set S) (W : Set S) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hle hxp)
  let p := W.map (algebraMap S (Localization.AtPrime 𝔐))
  have : p.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔐.primeCompl _ W inferInstance hdisj
  have hc : p.comap (algebraMap S (Localization.AtPrime 𝔐)) = W :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔐.primeCompl _ (I := W) inferInstance hdisj
  have h2 := h.localization_atPrime p
  have : IsLocalization W.primeCompl (Localization.AtPrime p) := by
    have h0 : IsLocalization (p.comap (algebraMap S (Localization.AtPrime 𝔐))).primeCompl
        (Localization.AtPrime p) := inferInstance
    convert h0 using 2
    rw [hc]
  let e := IsLocalization.algEquiv W.primeCompl (Localization.AtPrime W) (Localization.AtPrime p)
  exact h2.of_ringEquiv e.symm.toRingEquiv

theorem dimPIT_fin (F : Type) [Field F] (N : ℕ) (V W : Ideal (MvPolynomial (Fin N) F))
    (s : MvPolynomial (Fin N) F) (hV : V.IsPrime) (hs : s ∉ V)
    (hW : W ∈ (V ⊔ Ideal.span {s}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin N) F ⧸ W) + 1 =
      ringKrullDim (MvPolynomial (Fin N) F ⧸ V) := by
  apply GroundTheory.Heights₂.Heights.SectionComponents.ringKrullDim_quotient_add_one_eq <;>
    assumption

theorem dimPIT' : DimPITStatement := by
  intro F _ σ _ V W s hV hs hW
  let e : MvPolynomial σ F ≃+* MvPolynomial (Fin (Fintype.card σ)) F :=
    (MvPolynomial.renameEquiv F (Fintype.equivFin σ)).toRingEquiv
  let g : MvPolynomial (Fin (Fintype.card σ)) F →+* MvPolynomial σ F := e.symm
  let eh : MvPolynomial σ F →+* MvPolynomial (Fin (Fintype.card σ)) F := e
  have hcm : ∀ I : Ideal (MvPolynomial σ F), I.comap g = I.map eh := fun I => Ideal.comap_symm e
  have hV' : (V.map eh).IsPrime := by
    have h0 : (V.comap g).IsPrime := Ideal.comap_isPrime g V
    rwa [hcm] at h0
  have hs' : eh s ∉ V.map eh := by
    rw [← hcm, Ideal.mem_comap]
    simpa [g, eh] using hs
  have key := Ideal.comap_minimalPrimes_eq_of_surjective (f := g) e.symm.surjective
    (V ⊔ Ideal.span {s})
  have hmem : W.comap g ∈ ((V ⊔ Ideal.span {s}).comap g).minimalPrimes := key ▸ ⟨W, hW, rfl⟩
  rw [hcm, hcm, Ideal.map_sup, Ideal.map_span, Set.image_singleton] at hmem
  have := dimPIT_fin F _ _ _ _ hV' hs' hmem
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv W _ e rfl),
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V _ e rfl)]
  exact this

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimA =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimSt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim =====
