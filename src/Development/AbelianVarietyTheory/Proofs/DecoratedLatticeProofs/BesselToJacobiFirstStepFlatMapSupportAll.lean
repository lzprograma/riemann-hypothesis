module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColon
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnits
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewise
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlace
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorus, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorusStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlaceStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlace, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlaceStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMem, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMemStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramifiedStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZeroStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColonStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLines, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLinesStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlaceStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlace, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlaceStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgroStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnitsStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobi, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorus =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorus", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSe\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl

theorem oneBF_red_torus : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ n ∈ flagN J.d, n ∈ grpAt J.W (· = v) → ∀ t : GL (Fin ρ) (AE D), ∀ γ ∈ grpAt J.W₀ (· = v), ∀ κ, InK J.W LW (· = v) κ → 𝔉 (s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f) ≠ 0 → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf n hnN hnG t γ hγ κ hκ hne
  have h1 : InK B.V LV (· = v) 1 := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro y _
    simp
  have hfix : s.om (1, κ) f = f :=
    _root_.GlobalTheory.StabSetFix.stab_fix_vac D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hG.sdV hG.sdW (· = v)
      (fun w hw => hw ▸ ⟨hG.tame, hU.1, hU.2⟩) f hf 1 κ h1 hκ
  have hg : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ f hf.1
  have hsplit : s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f =
      s.om (1, n * J.d.emb0 γ) (s.om (1, J.d.levi t) f) := by
    have : n * J.d.levi t * J.d.emb0 γ * κ = (n * J.d.emb0 γ) * J.d.levi t * κ := by
      rw [mul_assoc n (J.d.levi t), ← J.d.wittHyperbolic_anisotropic_commute_levi γ t]
      simp only [mul_assoc]
    rw [this]
    have e : ((1 : GA D B.V), (n * J.d.emb0 γ) * J.d.levi t * κ) =
        ((1, n * J.d.emb0 γ) * (1, J.d.levi t)) * (1, κ) := by
      simp
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix]
  intro h0
  apply hne
  rw [hsplit, h𝔉.equiv _ hg n hnN hnG γ hγ, h0]
  have : opA ψ J.d B.o B.ζ s.om₀ n γ 0 = 0 := by
    funext w
    simp [opA, jacT, heisO]
  rw [this, smul_zero]

end GlobalTheory.FinPl
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorus =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorusStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorusStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorus\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.besselToJacobiFlatMap_support_reduces_to_torus : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ n ∈ flagN J.d, n ∈ grpAt J.W (· = v) → ∀ t : GL (Fin ρ) (AE D), ∀ γ ∈ grpAt J.W₀ (· = v), ∀ κ, InK J.W LW (· = v) κ → 𝔉 (s.om (1, n * J.d.levi t * J.d.emb0 γ * κ) f) ≠ 0 → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 := by
  first | exact @GlobalTheory.FinPl.oneBF_red_torus
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorusStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlaceStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlaceStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.besselToJacobi_flatMap_vacuum_at_goodPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) := by
  first | exact @GlobalTheory.FinPl.VacFlat.flat_vac
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlaceStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlace =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlace", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl.DiagInt

theorem finMul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D :=
  GlobalTheory.HostAdeleIso.intAE_mul_mem D hx hy

theorem intAt_add {D : D7} {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {D : D7} {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact finMul ha.2 hb.2⟩

theorem mul_sub_one {D : D7} {v : Pl D} {a b : AE D} (ha : a - 1 ∈ intAt D (· = v)) (hb : b - 1 ∈ intAt D (· = v)) :
    a * b - 1 ∈ intAt D (· = v) := by
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [e]
  exact intAt_add (intAt_add (intAt_mul ha hb) ha) hb

theorem inv_diag_mul {R : Type*} [CommRing R] {ρ : ℕ} (t : GL (Fin ρ) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0)
    (j : Fin ρ) : (t⁻¹).1 j j * t.1 j j = 1 := by
  have h0 : (t⁻¹).1 * t.1 = 1 := t.inv_mul
  have h := congrFun (congrFun h0 j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h, Finset.sum_eq_single j]
  · intro k _ hk; rw [ht k j hk, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ j) h'

theorem diag_int : ∀ (D : D7) (ρ : ℕ) (v : Pl D) (t : GL (Fin ρ) (AE D)), (∀ i j, i ≠ j → t.1 i j = 0) → (∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → (∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v)) → (∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v)) → ∀ i, t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ρ v t ht _ hr hl
  have key : ∀ k : ℕ, ∀ i : Fin ρ, i.1 + k + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
    intro k
    induction k with
    | zero => intro i hi; exact hl i (by omega)
    | succ k ih =>
      intro i hi
      have hj : i.1 + 1 < ρ := by omega
      let j : Fin ρ := ⟨i.1 + 1, hj⟩
      have h1 := hr i j rfl
      have h2 := ih j (by simp [j]; omega)
      have e : t.1 i i = t.1 i i * (t⁻¹).1 j j * t.1 j j := by
        rw [mul_assoc, inv_diag_mul t ht j, mul_one]
      rw [e]
      exact mul_sub_one h1 h2
  intro i
  exact key (ρ - 1 - i.1) i (by omega)

end GlobalTheory.FinPl.DiagInt
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlace =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlaceStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlaceStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.diagonalAdelic_entries_congr_one_of_ratios_at_place : ∀ (D : D7) (ρ : ℕ) (v : Pl D) (t : GL (Fin ρ) (AE D)), (∀ i j, i ≠ j → t.1 i j = 0) → (∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → (∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v)) → (∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v)) → ∀ i, t.1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.DiagInt.diag_int
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlaceStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMem =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMem", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl

theorem inK_mul {D : D7} (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a b : GA D S) :
    InK S L P a → InK S L P b → InK S L P (a * b) := by
  rintro ⟨ha, hma⟩ ⟨hb, hmb⟩
  refine ⟨(grpAt S P).mul_mem ha hb, ?_⟩
  intro y hy
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := by
    intro i
    have : (mt S b *ᵥ y) i = ∑ j, mt S b i j * y j := rfl
    rw [this]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  have hmul : mt S (a * b) = mt S a * mt S b := rfl
  rw [hmul, ← Matrix.mulVec_mulVec]
  exact (hmb y hy).trans (hma _ hy')

end GlobalTheory.FinPl
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMem =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMemStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMemStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMem\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.inLatticeStabilizerAtPlaces_mul_of_mem : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a b : GA D S), InK S L P a → InK S L P b → InK S L P (a * b) := by
  first | exact @GlobalTheory.FinPl.inK_mul
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMemStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramifiedStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramifiedStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.inv_diag_torus_integral_besselJacobi_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.InvStep.inv_int
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramifiedStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZeroStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZeroStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal\npublic import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero\nimport Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff\nimport Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.FinPl.LastDiag (add_smul_mx exists_idemAt jX_pX_mem_latA mxAt_smul smul_eq_self smul_isHalf' symplO_add_right')
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.lastDiagonalEntry_torus_integral_of_flatMap_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) :=
  _root_.GlobalTheory.FinPl.LastDiag.last_diag_int
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZeroStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColonStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColonStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColon\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.integral_of_keeps_selfDualLatticeLineColon : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (x : AE D), x - 1 ∈ idAt D (· = v) → (∀ r ∈ idAt D (· = v), (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → ∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * x * a) ∈ latV S L (· = v)) → x - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.ColonInt.colon_int
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColonStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLines =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLines", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff\npublic import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl.RatioAA

variable {D : D7}

theorem incA_mul_tmul (b : D.host.E) (p : AF D.host.F) (z : D.host.E) :
    incA D b * (p ⊗ₜ[D.host.F] z) = p ⊗ₜ[D.host.F] (b * z) := by
  show (1 ⊗ₜ[D.host.F] b) * (p ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem colMul_add {m n : ℕ} (x : Mx D m n) (l : Fin n) (c c' : AE D) :
    colMul x l (c + c') = colMul x l c + colMul x l c' := by
  funext k; simp [colMul, add_mul]

theorem colMul_mul {m n : ℕ} (x : Mx D m n) (l : Fin n) (b c : AE D) :
    (fun k => b * colMul x l c k) = colMul x l (b * c) := by
  funext k; simp [colMul, mul_assoc]

theorem mul_mem_latMul {S : HSp D} {𝔞 𝔟 : Set D.host.E} {L L' : Lat S} {P : Pl D → Prop} (b : D.host.E)
    (h : ∀ a ∈ 𝔞, ∀ x ∈ L, ∃ a' ∈ 𝔟, ∃ x' ∈ L', ∀ i, b * (a * x i) = a' * x' i)
    {y : Fin S.rank → AE D} (hy : y ∈ latMul S 𝔞 L P) : (fun i => incA D b * y i) ∈ latMul S 𝔟 L' P := by
  let f : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := (AddMonoidHom.mulLeft (incA D b)).compLeft (Fin S.rank)
  have hle : latMul S 𝔞 L P ≤ (latMul S 𝔟 L' P).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hs, a, ha, x, hx, rfl⟩
    obtain ⟨a', ha', x', hx', e⟩ := h a ha x hx
    refine AddSubgroup.subset_closure ⟨α, hα, hs, a', ha', x', hx', ?_⟩
    funext i
    show incA D b * _ = _
    rw [incA_mul_tmul, e]
  exact hle hy

theorem latV_to_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {α : D.host.E} (hα : α ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => incA D α * y i) ∈ latA S L P :=
  mul_mem_latMul α (fun a ha x hx => ⟨α, hα, x, hx, fun i => by rw [Set.mem_singleton_iff.1 ha]; ring⟩) hy

theorem latA_to_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} (hAA : D.host.AA ≠ 0) {β : D.host.E}
    (hβ : β ∈ D.host.AA⁻¹) {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : (fun i => incA D β * y i) ∈ latV S L P := by
  refine mul_mem_latMul β (fun a ha x hx => ?_) hy
  have hm : β * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [← inv_mul_cancel₀ hAA]; exact FractionalIdeal.mul_mem_mul hβ ha
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  refine ⟨1, rfl, o • x, L.smul_mem o hx, fun i => ?_⟩
  rw [Pi.smul_apply, Algebra.smul_def, ho]; ring

theorem latA_eq_zero (hAA : D.host.AA = 0) {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latA S L P) : y = 0 := by
  have hle : latA S L P ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hs, a, ha, x, hx, rfl⟩
    have ha0 : a = 0 := by
      have : a ∈ D.host.AA := ha
      rw [hAA] at this; exact (FractionalIdeal.mem_zero_iff _).1 this
    funext i
    simp [ha0]
  simpa using hle hy

theorem idAt_eq_zero_of_AA (hAA : D.host.AA = 0) {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ)
    (LV : Lat V) (LW : Lat W) (v : Pl D) (hsdV : IsSelfDualC V LV) (hC : ColsAt dV dW.jX LV LW v) (i : Fin ρ)
    (a : AE D) (ha : a ∈ idAt D (· = v)) : a = 0 := by
  have hs := GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)
  rw [mul_one] at hs
  have hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩
  set ε := pairA D.host.F 0 (singleV D.host.F v 1) with hεdef
  obtain ⟨N, hN, -, hNL⟩ := GlobalTheory.LatAlmostStd.exists_commensurable LV
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V LV hsdV)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 D.host.E))
    (fun k => dV.e k i)
  choose o ho using hb
  set x : Fin V.rank → D.host.E := ∑ k, Pi.single k (N • ((o k : 𝓞 D.host.E) : D.host.E)) with hxdef
  have hx : x ∈ LV := sum_mem fun k _ => hNL k (o k)
  have hxk : ∀ k, x k = N • (((b : 𝓞 D.host.E) : D.host.E) * dV.e k i) := by
    intro k
    rw [hxdef, Finset.sum_apply, Finset.sum_eq_single k (fun l _ hl => Pi.single_eq_of_ne' hl _)
      (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same]
    congr 1
    rw [show ((o k : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (o k) from rfl, ho k]
    first | rfl
  set t : D.host.E := N • ((b : 𝓞 D.host.E) : D.host.E) with htdef
  set c : AE D := ε ⊗ₜ[D.host.F] t with hcdef
  have hc : c ∈ idAt D (· = v) := GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _
  have hyc : colMul dV.jX i c ∈ latV V LV (· = v) := by
    refine AddSubgroup.subset_closure ⟨_, hs.1, hs.2, 1, rfl, x, hx, ?_⟩
    funext k
    rw [one_mul, hxk k]
    show c * incA D (dV.e k i) = _
    rw [mul_comm, incA_mul_tmul, htdef]
    congr 1
    rw [mul_smul_comm, mul_comm (dV.e k i)]
  have hW := latA_eq_zero hAA ((hC i c hc).1 hyc)
  have hc0 : c = 0 := by
    have hpX : dW.pX * dW.jX = 1 := by
      change (dW.e'ᴴ * W.gram).map (incA D) * dW.e.map (incA D) = 1
      rw [← Matrix.map_mul, dW.e'e]
      exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
    have h1 := congrFun (congrFun hpX i) i
    rw [Matrix.one_apply_eq, Matrix.mul_apply] at h1
    rw [← mul_one c, ← h1, Finset.mul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := congrFun hW k
    simp only [colMul, Pi.zero_apply] at this
    rw [mul_comm (dW.pX i k), ← mul_assoc, this, zero_mul]
  have ht : t ≠ 0 := by
    rw [htdef]
    refine smul_ne_zero hN ?_
    exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have hεc : algebraMap (AF D.host.F) (AE D) ε = c * incA D t⁻¹ := by
    rw [hcdef, mul_comm, incA_mul_tmul, inv_mul_cancel₀ ht]; rfl
  rw [← ((placeIdem_acts D v ε hp).1 a).1 ha, hεc, hc0, zero_mul, zero_mul]

end GlobalTheory.FinPl.RatioAA

open GlobalTheory.FinPl.RatioAA in
theorem GlobalTheory.FinPl.ratio_of_colsAt : ∀ (D : D7) (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i j : Fin ρ) (r : AE D), r ∈ idAt D (· = v) → (∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (r * a) ∈ latV V LV (· = v)) → ∀ a ∈ idAt D (· = v), colMul dW.jX j a ∈ latV W LW (· = v) → colMul dW.jX i (r * a) ∈ latV W LW (· = v) := by
  intro D V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v _ hsdV _ _ _ hC i j r hr H a ha hja
  by_cases hAA : D.host.AA = 0
  · rw [idAt_eq_zero_of_AA hAA dV dW LV LW v hsdV hC i a ha, mul_zero]
    have : colMul dW.jX i (0 : AE D) = 0 := by funext k; simp [colMul]
    rw [this]; exact zero_mem _
  · have key : ∀ t ∈ D.host.AA * D.host.AA⁻¹, colMul dW.jX i (incA D t * (r * a)) ∈ latV W LW (· = v) := by
      intro t ht
      refine FractionalIdeal.mul_induction_on ht (fun α hα β hβ => ?_) (fun x y hx hy => ?_)
      · have h1 := latV_to_latA hα hja
        rw [colMul_mul] at h1
        have hαa : incA D α * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ha
        have h2 := (hC j _ hαa).2 h1
        have h3 := H _ h2
        have h4 := (hC i _ (Ideal.mul_mem_left _ r hαa)).1 h3
        have h5 := latA_to_latV hAA hβ h4
        rw [colMul_mul] at h5
        convert h5 using 2
        rw [map_mul]; ring
      · rw [map_add (f := _), add_mul, colMul_add]; exact add_mem hx hy
    have := key 1 (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)
    simpa using this
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLines =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLinesStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLinesStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLines\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.latticeLineRatio_transport_of_columnsCarryLines : ∀ (D : D7) (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i j : Fin ρ) (r : AE D), r ∈ idAt D (· = v) → (∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (r * a) ∈ latV V LV (· = v)) → ∀ a ∈ idAt D (· = v), colMul dW.jX j a ∈ latV W LW (· = v) → colMul dW.jX i (r * a) ∈ latV W LW (· = v) := by
  first | exact @GlobalTheory.FinPl.ratio_of_colsAt
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLinesStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlaceStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlaceStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.wittLeviTransvection_mem_compactAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (hij : i ≠ j) (r : AE D), r ∈ idAt D (· = v) → (∀ a ∈ idAt D (· = v), colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → InK S L (· = v) (d.levi (GlobalTheory.GLGen.transvGL hij r)) := by
  first | exact @GlobalTheory.FinPl.RootKeep.inK_levi_transv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlaceStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlace =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlace", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColonStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLinesStatement\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSe\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlaceStatement\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl.RatioStep

variable {D : D7}

theorem mul_mem_intAt {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ha.2 hb.2⟩

theorem diag_inv {ρ : ℕ} (t : GL (Fin ρ) (AE D)) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    t.1 = diagonal (fun k => t.1 k k) ∧ (t⁻¹).1 = diagonal (fun k => (t⁻¹).1 k k) ∧
      ∀ k, t.1 k k * (t⁻¹).1 k k = 1 :=
  GlobalTheory.FinPl.InvStep.diag_inv t ht

theorem conj_transv {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (t : GL (Fin ρ) (AE D))
    (ht : ∀ i j, i ≠ j → t.1 i j = 0) {i j : Fin ρ} (hij : i ≠ j) (c : AE D) :
    (d.levi t)⁻¹ * d.levi (GlobalTheory.GLGen.transvGL hij c) * d.levi t =
      d.levi (GlobalTheory.GLGen.transvGL hij ((t⁻¹).1 i i * c * t.1 j j)) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  obtain ⟨h1, h2, h3⟩ := diag_inv t ht
  ext : 1
  rw [Units.val_mul, Units.val_mul]
  show (t⁻¹).1 * Matrix.transvection i j c * t.1 = Matrix.transvection i j ((t⁻¹).1 i i * c * t.1 j j)
  conv_lhs => rw [h2, h1]
  exact GlobalTheory.GLGen.diag_transv_diag _ _ (fun k => by rw [mul_comm]; exact h3 k) hij c

theorem transv_mem_UX {ρ : ℕ} {i j : Fin ρ} (hij : i ≠ j) (hlt : i < j) (c : AE D) :
    GlobalTheory.GLGen.transvGL hij c ∈ UX D ρ := by
  rw [mem_UX]
  intro a b
  show (b < a → (Matrix.transvection i j c) a b = 0) ∧ (Matrix.transvection i j c) a a = 1
  refine ⟨fun hba => ?_, ?_⟩
  · simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    rw [one_apply_ne (ne_of_gt hba), zero_add, ite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact absurd (hba.trans hlt) (lt_irrefl _)
  · simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, one_apply_eq]
    rw [ite_eq_right, add_zero]
    rintro ⟨rfl, e⟩
    exact hij e.symm

theorem upSum_transv {ρ : ℕ} {i j : Fin ρ} (hij : i ≠ j) (hj : j.1 = i.1 + 1) (c : AE D) :
    upSum (GlobalTheory.GLGen.transvGL hij c : GL (Fin ρ) (AE D)).1 = c := by
  have e : (GlobalTheory.GLGen.transvGL hij c : GL (Fin ρ) (AE D)).1 = Matrix.transvection i j c := rfl
  rw [e]
  unfold upSum
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · rw [ite_eq_left hj]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, one_apply_ne hij, and_self, ite_true, zero_add]
  · intro b _ hb
    rw [ite_eq_right]
    intro h
    exact hb (Fin.ext (by omega))
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h
    · have hbk : b ≠ k := fun e => by rw [e] at h; omega
      simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply, one_apply_ne hbk, zero_add]
      rw [ite_eq_right]
      rintro ⟨rfl, -⟩
      exact hb rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem levi_sub_one_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {t : GL (Fin ρ) (AE D)}
    (ht : d.levi t ∈ grpAt S P) (i j : Fin ρ) : t.1 i j - (1 : Mx D ρ ρ) i j ∈ idAt D P :=
  GlobalTheory.FinPl.InvStep.levi_sub_one_mem d ht i j

theorem opA_levi_one (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (om : Om V₀ W₀) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ)
    (Ξ : WO V₀ W₀ → ℂ) : opA ψ dW o ζ om (dW.levi u) 1 Ξ = Ξ := by
  unfold opA
  rw [show dW.levi u = dW.levi u * 1 from (mul_one _).symm, jacT_levi_mul ψ dW V₀ _ (yZero_mul V₀ _ hu),
    jacT_one]
  show (om (1, 1)) Ξ = Ξ
  rw [show ((1 : GA D V₀), (1 : GA D W₀)) = 1 from rfl, map_one]
  rfl

theorem psiFlag_transv (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {i j : Fin ρ}
    (hij : i ≠ j) (hj : j.1 = i.1 + 1) (c : AE D) :
    psiFlag ψ d (d.levi (GlobalTheory.GLGen.transvGL hij c)) = psiE ψ c := by
  rw [psiFlag, blockX_levi, upSum_transv hij hj c]

theorem psi_root {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {v : Pl D}
    (hG : GoodBF ψ B J LV LV₀ LW LW₀ v) (hU : UnrAt s v) {𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)}
    (hF : IsFlatBF s (· = v) 𝔉) {f : WO B.V J.W → ℂ} (hf : Vac ψ B.V J.W LV LW (· = v) f)
    (t : GL (Fin ρ) (AE D)) (ht : J.d.levi t ∈ grpAt J.W (· = v)) (hne : 𝔉 (s.om (1, J.d.levi t) f) ≠ 0)
    {i j : Fin ρ} (hij : i ≠ j) (hlt : i < j) (hj : j.1 = i.1 + 1) (c : AE D)
    (hK : InK J.W LW (· = v) ((J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t)) :
    psiE ψ c = 1 := by
  have hu : GlobalTheory.GLGen.transvGL hij c ∈ UX D ρ := transv_mem_UX hij hlt c
  have hnF : J.d.levi (GlobalTheory.GLGen.transvGL hij c) ∈ flagN J.d := J.d.levi_mem_NFlag hu
  have hnG : J.d.levi (GlobalTheory.GLGen.transvGL hij c) ∈ grpAt J.W (· = v) := by
    have e : J.d.levi (GlobalTheory.GLGen.transvGL hij c) = J.d.levi t *
        ((J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t) * (J.d.levi t)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem ht hK.1) (inv_mem ht)
  have hθ : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hf.1
  have h1K : InK B.V LV (· = v) 1 := ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩
  have hfix : s.om (1, (J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t) f = f :=
    _root_.GlobalTheory.StabSetFix.stab_fix_vac D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hG.sdV hG.sdW (· = v)
      (by rintro w rfl; exact ⟨hG.tame, hU.1, hU.2⟩) f hf 1 _ h1K hK
  have hom : s.om (1, J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.emb0 1) (s.om (1, J.d.levi t) f) =
      s.om (1, J.d.levi t) f := by
    rw [map_one, mul_one]
    have e : (1, J.d.levi (GlobalTheory.GLGen.transvGL hij c)) * ((1 : GA D B.V), J.d.levi t) =
        ((1 : GA D B.V), J.d.levi t) *
          (1, (J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij c) * J.d.levi t) := by
      simp only [Prod.mk_mul_mk, one_mul]
      congr 1
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hfix]
  have heq := hF.equiv _ hθ _ hnF hnG 1 (one_mem _)
  have hψ := psiFlag_transv ψ J.d hij hj c
  rw [hom] at heq
  have hA : opA ψ J.d B.o B.ζ s.om₀ (J.d.levi (GlobalTheory.GLGen.transvGL hij c)) 1 (𝔉 (s.om (1, J.d.levi t) f)) =
      𝔉 (s.om (1, J.d.levi t) f) := opA_levi_one ψ J.d B.o B.ζ s.om₀ hu _
  rw [hA, hψ] at heq
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
  have h1 := congrFun heq w
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hw
  have h2 : star (psiE ψ c) = 1 := mul_right_cancel₀ hw (h1.symm.trans (one_mul _).symm)
  rw [← star_star (psiE ψ c), h2, star_one]

theorem ratio_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 hF f hf t htd ht hne i j hj
  have hij : i ≠ j := fun e => by rw [e] at hj; omega
  have hlt : i < j := by rw [Fin.lt_def]; omega
  obtain ⟨-, -, h3⟩ := diag_inv t htd
  have hti : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d ht i i
    rwa [one_apply_eq] at this
  have htj : (t⁻¹).1 j j - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d (P := (· = v)) (t := t⁻¹) (by rw [map_inv]; exact inv_mem ht) j j
    rwa [one_apply_eq] at this
  have hx1 : t.1 i i * (t⁻¹).1 j j - 1 ∈ idAt D (· = v) := by
    have e : t.1 i i * (t⁻¹).1 j j - 1 = (t.1 i i - 1) * (t⁻¹).1 j j + ((t⁻¹).1 j j - 1) := by ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hti) htj
  refine GlobalTheory.T.integral_of_keeps_selfDualLatticeLineColon D B.V B.V₀ ρ B.d LV LV₀ v hG.tame hG.sdV hG.monoV i j _ hx1 ?_
  intro r hr hR
  have hP := hG.prim i j hj
  refine (hP (r * (t.1 i i * (t⁻¹).1 j j)) (Ideal.mul_mem_right _ _ hr)).2 ?_
  intro o ho
  have hψr := (hP r hr).1 hR
  have hro : r * o ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hr
  have hRo : ∀ a : AE D, colMul B.d.jX j a ∈ latV B.V LV (· = v) → colMul B.d.jX i (r * o * a) ∈ latV B.V LV (· = v) :=
    (hP (r * o) hro).2 fun o' ho' => by rw [mul_assoc]; exact hψr _ (mul_mem_intAt ho ho')
  have hWV := GlobalTheory.T.latticeLineRatio_transport_of_columnsCarryLines D B.V B.V₀ J.W J.W₀ ρ B.d J.d LV LV₀ LW LW₀ v hG.tame hG.sdV hG.sdW hG.monoV hG.monoW hG.cols
    i j (r * o) hro hRo
  have hK := GlobalTheory.T.wittLeviTransvection_mem_compactAtPlace D J.W J.W₀ ρ J.d LW LW₀ v hG.sdW hG.monoW i j hij (r * o) hro hWV
  have hc : (t⁻¹).1 i i * (r * o * (t.1 i i * (t⁻¹).1 j j)) * t.1 j j = r * o := by
    linear_combination (r * o * (t.1 j j * (t⁻¹).1 j j)) * h3 i + (r * o) * h3 j
  have hK' : InK J.W LW (· = v) ((J.d.levi t)⁻¹ * J.d.levi (GlobalTheory.GLGen.transvGL hij (r * o * (t.1 i i * (t⁻¹).1 j j))) *
      J.d.levi t) := by
    rw [conj_transv J.d t htd hij, hc]
    exact hK
  have := psi_root s hG hU hF hf t ht hne hij hlt hj _ hK'
  rwa [mul_right_comm r o] at this

end GlobalTheory.FinPl.RatioStep
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlace =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlaceStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlaceStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.torusEntryRatio_integral_at_unramified_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.RatioStep.ratio_int
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlaceStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgroStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgroStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgro\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.emb0_mem_grpAt_of_mem_grpAt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (P : Pl D → Prop) (g : GA D S₀), g ∈ grpAt S₀ P → d.emb0 g ∈ grpAt S P := by
  first | exact @GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgroStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnitsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnitsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnits\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.wittLeviDiagonal_mem_latticeStabilizer_of_units : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → d.levi t ∈ grpAt S (· = v) → (∀ i, t.1 i i - 1 ∈ intAt D (· = v) ∧ (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → InK S L (· = v) (d.levi t) := by
  first | exact @GlobalTheory.FinPl.LeviUnitK.inK_levi
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnitsStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobi =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobi", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapSupportReducesToTorusStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlaceStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlaceStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesMulOfMemStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramifiedStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZeroStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TorusEntryRatioIntegralAtUnramifiedPlaceStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgroStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnitsStatement\nimport Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi\nimport Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\nimport Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl

theorem oneCosetBF : ∀ D : D7, GlobalTheory.FinPl.OneCosetBF D := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf
  refine ⟨GlobalTheory.T.besselToJacobi_flatMap_vacuum_at_goodPlace D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf, ?_⟩
  intro h hh hne
  obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
    _root_.GlobalTheory.IwaPlace.iwasawa_at_place D J.W J.W₀ ρ J.d LW LW₀ v hG.tame hG.sdW hG.sdW₀ hG.monoW h hh
  have h1 := GlobalTheory.T.besselToJacobiFlatMap_support_reduces_to_torus D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf n hnN hnG t γ hγ κ hκ hne
  have hinv := GlobalTheory.T.inv_diag_torus_integral_besselJacobi_unramified D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hrat := GlobalTheory.T.torusEntryRatio_integral_at_unramified_place D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hlast := GlobalTheory.T.lastDiagonalEntry_torus_integral_of_flatMap_ne_zero D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hint := GlobalTheory.T.diagonalAdelic_entries_congr_one_of_ratios_at_place D ρ v t ht hinv hrat hlast
  have hK := GlobalTheory.T.wittLeviDiagonal_mem_latticeStabilizer_of_units D J.W J.W₀ ρ J.d LW LW₀ v hG.sdW hG.monoW t ht htG (fun i => ⟨hint i, hinv i⟩)
  refine ⟨n * J.d.emb0 γ, ?_, ?_, J.d.levi t * κ, GlobalTheory.T.inLatticeStabilizerAtPlaces_mul_of_mem D J.W LW (· = v) _ _ hK hκ, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right ⟨γ, rfl⟩)
  · exact Subgroup.mul_mem _ hnG (GlobalTheory.T.emb0_mem_grpAt_of_mem_grpAt D J.W J.W₀ ρ J.d (· = v) γ hγ)
  · rw [mul_assoc n (J.d.levi t), ← J.d.wittHyperbolic_anisotropic_commute_levi γ t]
    simp only [mul_assoc]

end GlobalTheory.FinPl
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobi =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua\npublic import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewise\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobi\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall\nimport Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSe\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl

variable {D : D7}

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (hIJ : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro x hx
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hx ⊢
  have e : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V x) =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ)
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V x)) := by
    ext i j
    simp
  rw [e, hx, map_one]

theorem grpOff_le_at (V : HSp D) {P : Pl D → Prop} {v : Pl D} (hv : P v) : grpOff V P ≤ grpOff V (· = v) := by
  apply congGrp_mono
  exact le_iInf fun w => iInf_le_of_le ⟨w.1, by rw [w.2]; exact hv⟩ le_rfl

theorem grpOff_eq_top (V : HSp D) {P : Pl D → Prop} (hP : ¬ ∃ v, P v) : grpOff V P = ⊤ := by
  have hI : idOff D P = ⊤ := by
    haveI : IsEmpty {w : Pl D // P w} := ⟨fun w => hP ⟨w.1, w.2⟩⟩
    simp [idOff]
  rw [grpOff, hI, eq_top_iff]
  intro x _
  haveI : Subsingleton (AE D ⧸ (⊤ : Ideal (AE D))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Subsingleton.elim _ _

theorem grpAt_eq_bot (V : HSp D) {P : Pl D → Prop} (hP : ¬ ∃ v, P v) : grpAt V P = ⊥ := by
  have h := ((_root_.GlobalTheory.FinPl.localComponents D P).2 V).2.2.1
  rwa [grpOff_eq_top V hP, inf_top_eq] at h

theorem latO_eq_bot (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P : Pl D → Prop} (hP : ¬ ∃ v, P v) : latO S T LS LT P = ⊥ := by
  rw [latO, AddSubgroup.closure_eq_bot_iff]
  rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
  have h0 : α = 0 := by
    exact RestrictedProduct.ext _ _ fun v => hα v fun h => hP ⟨v, h⟩
  subst h0
  ext i j
  simp only [pairA, Prod.mk_zero_zero, Matrix.of_apply, Matrix.zero_apply]
  exact TensorProduct.zero_tmul _ _

alias heisO_zero_eq := _root_.GlobalTheory.SplitScalar.heisO_zero

theorem suppFirst_holds (D : D7) : SuppFirst D := by
  intro ψ ρ B J s LV LV₀ LW LW₀ P hgood hunr hsdW Φ hΦ
  refine ⟨?_, fun g hg => ⟨?_, ?_⟩⟩
  · intro κ κ' hκ hκ'
    by_cases hP : ∃ v, P v
    · obtain ⟨v, hv⟩ := hP
      exact _root_.GlobalTheory.StabSetFix.stab_fix_vac D ψ B.V J.W s.χV s.χW s.om s.weil LV LW (hgood v hv).sdV hsdW P
        (fun w hw => ⟨(hgood w hw).tame, (hunr w hw).1, (hunr w hw).2⟩) Φ hΦ κ κ' hκ hκ'
    · have h1 : κ = 1 := Subgroup.mem_bot.mp (grpAt_eq_bot B.V hP ▸ hκ.1)
      have h2 : κ' = 1 := Subgroup.mem_bot.mp (grpAt_eq_bot J.W hP ▸ hκ'.1)
      subst h1 h2
      rw [Prod.mk_one_one, map_one]
      rfl
  · intro h hne
    refine _root_.GlobalTheory.FinPl.placesToAdeles D J.W LW P hsdW (jacGrp J.d) h ?_
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := ((_root_.GlobalTheory.FinPl.localComponents D (· = v)).2 J.W).1 h
    refine ⟨x, hx, y, hy, rfl, ?_⟩
    have hsdV := (hgood v hv).sdV
    have htameP : ∀ w, P w → Tame D w := fun w hw => (hgood w hw).tame
    have htame1 : ∀ w : Pl D, w = v → Tame D w := fun w hw => hw ▸ htameP v hv
    have hΦv : Vac ψ B.V J.W LV LW (· = v) Φ :=
      ((_root_.GlobalTheory.VacLoc.vac_loc D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hsdV hsdW P htameP Φ).1.mp hΦ).2 v hv
    have hf : Vac ψ B.V J.W LV LW (· = v) (s.om (g, y) Φ) :=
      (_root_.GlobalTheory.VacLoc.vac_loc D ψ B.V J.W s.χV s.χW s.om s.weil LV LW hsdV hsdW (· = v) htame1 Φ).2.1 hΦv g
        (grpOff_le_at B.V hv hg) y hy
    refine (_root_.GlobalTheory.FinPl.oneCosetBF D ψ ρ B J s LV LV₀ LW LW₀ v (hgood v hv) (hunr v hv) (flatBF s)
      ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).1 ρ B J s) _ hf).2 x hx ?_
    have e : s.om (1, x) (s.om (g, y) Φ) = s.om (g, x * y) Φ := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e]
    exact hne
  · intro h hh
    by_cases hP : ∃ v, P v
    · obtain ⟨v₀, hv₀⟩ := hP
      have htameP : ∀ w, P w → Tame D w := fun w hw => (hgood w hw).tame
      have hvacP := _root_.GlobalTheory.VacLoc.vac_loc D ψ B.V J.W s.χV s.χW s.om s.weil LV LW (hgood v₀ hv₀).sdV hsdW P htameP
      have hf : Vac ψ B.V J.W LV LW P (s.om (g, h) Φ) := (hvacP Φ).2.1 hΦ g hg h hh
      refine ((_root_.GlobalTheory.VacLoc.vac_loc D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ LV₀ LW₀ (hgood v₀ hv₀).sdV₀ (hgood v₀ hv₀).sdW₀ P
        htameP _).1.mpr ⟨?_, ?_⟩)
      · exact ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂.theta _ hf.1
      · intro v hv
        have hfv := ((hvacP _).1.mp hf).2 v hv
        exact (_root_.GlobalTheory.FinPl.oneCosetBF D ψ ρ B J s LV LV₀ LW LW₀ v (hgood v hv) (hunr v hv) (flatBF s)
          ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).1 ρ B J s) _ hfv).1
    · refine ⟨((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P).1 ρ B J s).Heisenberg₂.theta _ (s.weil.om_pres _ _ hΦ.1), ?_⟩
      rw [latO_eq_bot _ _ _ _ hP]
      refine ⟨fun u hu => ?_, fun e _ u hu _ => ?_⟩
      · rw [AddSubgroup.mem_bot.mp hu, nsmul_zero, heisO_zero_eq]
      · rw [AddSubgroup.mem_bot.mp hu, heisO_zero_eq]

end GlobalTheory.FinPl

theorem GlobalTheory.FinPl.suppFirst_all : ∀ D : D7, GlobalTheory.FinPl.SuppFirst D := GlobalTheory.FinPl.suppFirst_holds
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAll =====
