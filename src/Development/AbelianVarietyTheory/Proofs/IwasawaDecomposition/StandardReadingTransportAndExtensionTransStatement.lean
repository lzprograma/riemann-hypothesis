module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLiftsStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntermediateCoefficientPlaceBetween, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargementStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdCopy, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtensionStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTrans, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTransStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLiftsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLiftsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLifts\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLiftsStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntermediateCoefficientPlaceBetween =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntermediateCoefficientPlaceBetween", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.Top.Bl

theorem exists_below_between : ∀ (D₁ D₂ D₃ : Formalism.BasicNotions.D7), Set.range D₂.what₂.embLL ⊆ Set.range D₃.what₂.embLL → ∀ (v₁ : D₁.what₂.places.Pl) (v₃ : D₃.what₂.places.Pl), GlobalTheory.Mem.Top.Bl.Below D₁ D₃ v₁ v₃ → ∃ v₂ : D₂.what₂.places.Pl, GlobalTheory.Mem.Top.Bl.Below D₁ D₂ v₁ v₂ ∧ GlobalTheory.Mem.Top.Bl.Below D₂ D₃ v₂ v₃ := by
  intro D₁ D₂ D₃ hR v₁ v₃ h13

  have hmem : ∀ x : D₂.what₂.LL, D₂.what₂.embLL x ∈ D₃.what₂.embLL.fieldRange := fun x => by
    obtain ⟨y, hy⟩ := hR ⟨x, rfl⟩
    exact ⟨y, hy⟩
  let ι : D₂.what₂.LL →+* D₃.what₂.LL :=
    (D₃.what₂.embLL.rangeRestrictFieldEquiv).symm.toRingHom.comp (D₂.what₂.embLL.codRestrict _ hmem)
  have hι : ∀ x, D₃.what₂.embLL (ι x) = D₂.what₂.embLL x := fun x => by
    have := (D₃.what₂.embLL.rangeRestrictFieldEquiv).apply_symm_apply ⟨D₂.what₂.embLL x, hmem x⟩
    exact congrArg Subtype.val this
  let ιO : 𝓞 D₂.what₂.LL →+* 𝓞 D₃.what₂.LL := RingOfIntegers.mapRingHom ι
  have hιO : ∀ x : 𝓞 D₂.what₂.LL, ((ιO x : 𝓞 D₃.what₂.LL) : D₃.what₂.LL) = ι (x : D₂.what₂.LL) := fun x => rfl
  set Q := (D₃.plEq v₃).asIdeal with hQ
  let P : Ideal (𝓞 D₂.what₂.LL) := Q.comap ιO
  have hPprime : P.IsPrime := Ideal.comap_isPrime ιO Q
  have hQne : Q ≠ ⊥ := (D₃.plEq v₃).ne_bot
  have hn : Ideal.absNorm Q ≠ 0 := by
    intro h; exact hQne (Ideal.absNorm_eq_zero_iff.mp h)
  have hPne : P ≠ ⊥ := by
    intro h
    have hin : ((Ideal.absNorm Q : ℕ) : 𝓞 D₂.what₂.LL) ∈ P := by
      show ιO _ ∈ Q
      rw [map_natCast]; exact Ideal.absNorm_mem Q
    rw [h, Ideal.mem_bot] at hin
    exact hn (by exact_mod_cast hin)
  refine ⟨D₂.plEq.symm ⟨P, hPprime, hPne⟩, ?_, ?_⟩
  · intro x₁ x₂ hx
    rw [Equiv.apply_symm_apply]
    show x₁ ∈ (D₁.plEq v₁).asIdeal ↔ ιO x₂ ∈ Q
    exact h13 x₁ (ιO x₂) (by rw [hιO, hι]; exact hx)
  · intro x₂ x₃ hx
    rw [Equiv.apply_symm_apply]
    show ιO x₂ ∈ Q ↔ x₃ ∈ Q
    have : ιO x₂ = x₃ := by
      apply Subtype.ext
      apply D₃.what₂.embLL.injective
      show D₃.what₂.embLL (ι (x₂ : D₂.what₂.LL)) = _
      rw [hι]; exact hx
    rw [this]

end GlobalTheory.Mem.Top.Bl
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntermediateCoefficientPlaceBetween =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargementStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargementStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement\nimport Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\nimport Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction\nimport Formalism.LocalToGlobal.IndefiniteReal.RecTie\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargementStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdCopy =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdCopy", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StdTr

theorem std_copy (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w.st Z') w.I hX T Wt) : z'.Xg = z.Xg → z'.tr = z.tr → HEq z'.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) → HEq z'.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.core) → z.Std → z'.Std := by
  intro hXg htr hR hc hs
  cases z' with
  | @mk Xg' tr' core' alg' alg_eq' R' cG' geo' pins' lev' idG' good' mu' le' ks' =>
  dsimp only at hXg htr hR hc ⊢
  subst hXg htr
  obtain rfl := eq_of_heq hc
  change BrgStd (w.st Z') w.I hX (usedOf w.I T Wt) z.Xg z.tr R'.toRealDat
  change HEq R' _ at hR
  have e : alg' = alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.st Z').B.embLL.injective
    rw [alg_eq']
    exact (z.alg_eq y).symm
  clear cG' geo' pins' lev' idG' good' mu' le' ks' alg_eq' hc
  subst e
  obtain rfl := eq_of_heq hR
  exact (by with_unfolding_all exact (hs :))

end GlobalTheory.Mem.R3.Rw.StdTr
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdCopy =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtensionStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtensionStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtensionStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTrans =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTrans", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLiftsStatement\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntermediateCoefficientPlaceBetween\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargementStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdCopy\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtensionStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StdTr

theorem heq_fin_apply {m m' : ℕ} {f : Fin m → ℕ} {g : Fin m' → ℕ} (h : HEq g f) (hm : m' = m) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') : g i' = f i := by
  subst hm
  cases h
  exact congrArg g (Fin.ext hi.symm)

theorem heq_fin_mid {m m' : ℕ} {f : Fin m → ℕ} {g : Fin m' → ℕ} (h : HEq g f) (hm : m' = m) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') (k : Fin (f i)) : ∃ k' : Fin (g i'), (k : ℕ) = k' :=
  ⟨⟨k, lt_of_lt_of_eq k.2 (heq_fin_apply h hm i i' hi).symm⟩, rfl⟩

theorem heq_mid {α β : Type} (h : β = α) (a : α) : ∃ b : β, HEq b a := ⟨cast h.symm a, cast_heq _ _⟩

theorem ext_trans {B₁ B₂ B₃ : Base} {f₁ f₂ f₃ T₁ T₂ T₃} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {w₃ : ColW B₃ f₃ T₃} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {Z₃ : w₃.Lt} {h₁ h₂ h₃ W₁ W₂ W₃} {z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁} {z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂} {z₃ : Dat (w₃.st Z₃) w₃.I h₃ T₃ W₃} (e₁₂ : Enl B₁ B₂) (e₂₃ : Enl B₂ B₃) (x : Ext z₁ z₂) (y : Ext z₂ z₃) :
    Ext z₁ z₃ := by
  have hmm : (w₂.st Z₂).toD7.R.m = (w₁.st Z₁).toD7.R.m := congrArg (fun P : Pre => P.R.m) e₁₂.1
  have hm : ∀ i : Fin (w₁.st Z₁).toD7.R.m, ∃ i' : Fin (w₂.st Z₂).toD7.R.m, (i : ℕ) = i' :=
    fun i => ⟨⟨i, lt_of_lt_of_eq i.2 hmm.symm⟩, rfl⟩
  refine @Ext.mk B₁ B₃ f₁ f₃ T₁ T₃ w₁ w₃ Z₁ Z₃ h₁ h₃ W₁ W₃ z₁ z₃ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact HEq.trans y.H x.H
  · exact HEq.trans y.l x.l
  · exact HEq.trans y.c x.c
  · exact HEq.trans y.Dw x.Dw
  · exact HEq.trans y.Xo x.Xo
  · exact HEq.trans y.U x.U
  · exact HEq.trans y.V x.V
  · exact HEq.trans y.dict x.dict
  · exact HEq.trans y.mu x.mu
  · exact HEq.trans y.Kf x.Kf
  · exact HEq.trans y.cE x.cE
  · exact HEq.trans y.chiW x.chiW
  · exact HEq.trans y.x₀ x.x₀
  · exact HEq.trans y.iota x.iota
  · exact HEq.trans y.ψ x.ψ
  · exact HEq.trans y.θ x.θ
  · exact HEq.trans y.βW x.βW
  · exact HEq.trans y.βY x.βY
  · exact HEq.trans y.nW x.nW
  · exact HEq.trans y.βV x.βV
  · exact HEq.trans y.ΛV x.ΛV
  · exact HEq.trans y.ΛW x.ΛW
  · exact HEq.trans y.Pg x.Pg
  · exact HEq.trans y.eG x.eG
  · exact HEq.trans y.Sb x.Sb
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.BV i i' hi'
    have b := y.BV i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.1 a.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.1 a.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.1 a.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.1 a.2.2.2.2.1
    exact HEq.trans b.2.2.2.2.2 a.2.2.2.2.2
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.MW i i' hi'
    have b := y.MW i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.1) (a.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.1) (a.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.1) (a.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.1) (a.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.1) (a.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.1) (a.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.2.2.2.1)
    intro φ φ'' hφ
    refine Exists.elim (heq_mid (GlobalTheory.Mem.R3.Rw.Ext.cuspA_type_eq z₁ z₂ e₁₂ x i i' hi') φ) fun φ' hφ' => ?_
    exact HEq.trans (b.2.2.2.2.2.2.2.2.2.2 φ' φ'' (HEq.trans hφ hφ'.symm)) (a.2.2.2.2.2.2.2.2.2.2 φ φ' hφ')
  · intro i i'' h φ φ'' hφ k k'' hk
    refine Exists.elim (hm i) fun i' hi' => ?_
    refine Exists.elim (heq_mid (GlobalTheory.Mem.R3.Rw.Ext.cuspA_type_eq z₁ z₂ e₁₂ x i i' hi') φ) fun φ' hφ' => ?_
    refine Exists.elim (heq_fin_mid x.nW hmm i i' hi' k) fun k' hk' => ?_
    exact Eq.trans (y.forms i' i'' (hi'.symm.trans h) φ' φ'' (HEq.trans hφ hφ'.symm) k' k'' (hk'.symm.trans hk)) (x.forms i i' hi' φ φ' hφ' k k' hk')
  · intro v v'' hB
    refine Exists.elim (_root_.GlobalTheory.Mem.Top.Bl.exists_below_between (w₁.D Z₁) (w₂.D Z₂) (w₃.D Z₃) e₂₃.2.2.2 v v'' hB) fun v' h => ?_
    exact Iff.trans (x.W1 v v' h.1) (y.W1 v' v'' h.2)
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.cV i i' hi'
    have b := y.cV i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    exact HEq.trans b.2 a.2
  · exact HEq.trans y.pb x.pb
  · exact HEq.trans y.ΛY x.ΛY
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.κ i i' hi'
    have b := y.κ i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.1 a.2.1
    exact Eq.trans b.2.2 a.2.2
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.ref i i' hi'
    have b := y.ref i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.1 a.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.1 a.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.1 a.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.1 a.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.2.1 a.2.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.2.2.1 a.2.2.2.2.2.2.1
    exact HEq.trans b.2.2.2.2.2.2.2 a.2.2.2.2.2.2.2
  · intro i i'' h ok ok'' φ φ'' C
    refine Exists.elim (hm i) fun i' hi' => ?_
    have hv : HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs := by
      have a := heq_of_eq z₂.lev.Pg.symm
      have b := heq_of_eq z₁.lev.Pg
      exact HEq.trans (HEq.trans a x.Pg) b
    have L := GlobalTheory.Mem.R3.Tr.lift_refTuple_enl w₁ w₂ W₁ W₂ e₁₂ hv (GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi_ext z₁ z₂ e₁₂ x) ((i : ℕ) + 1) ((i' : ℕ) + 1) (congrArg (· + 1) hi')
    refine Exists.elim (L.2 φ) fun φ' C' => ?_
    have ok' : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 ((i' : ℕ) + 1)).Ok := Formalism.L2.Col.mtKOk _ _ _ _ h₂ _
    have a := x.jL i i' hi' ok ok' φ φ' C'
    have b := y.jL i' i'' (hi'.symm.trans h) ok' ok'' φ' φ'' fun d' d'' hd => by
      refine Exists.elim (heq_mid L.1.symm d') fun d hd' => ?_
      exact HEq.trans (C d d'' (HEq.trans hd hd'.symm)) (HEq.symm (C' d d' hd'.symm))
    exact HEq.trans b a

theorem std_copy_and_ext_trans : (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w.st Z') w.I hX T Wt), z'.Xg = z.Xg → z'.tr = z.tr → HEq z'.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) → HEq z'.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.core) → z.Std → z'.Std) ∧ ∀ (B₁ B₂ B₃ : Base) f₁ f₂ f₃ T₁ T₂ T₃ (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (w₃ : ColW B₃ f₃ T₃) (Z₁ : w₁.Lt) (Z₂ : w₂.Lt) (Z₃ : w₃.Lt) h₁ h₂ h₃ W₁ W₂ W₃ (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂) (z₃ : Dat (w₃.st Z₃) w₃.I h₃ T₃ W₃), Enl B₁ B₂ → Enl B₂ B₃ → Ext z₁ z₂ → Ext z₂ z₃ → Ext z₁ z₃ :=
  ⟨std_copy, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁₂ e₂₃ x y => ext_trans e₁₂ e₂₃ x y⟩

end GlobalTheory.Mem.R3.Rw.StdTr
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTrans =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTransStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTransStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTrans\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

alias _root_.GlobalTheory.T.standardReading_transport_and_extension_trans := _root_.GlobalTheory.Mem.R3.Rw.StdTr.std_copy_and_ext_trans
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTransStatement =====
