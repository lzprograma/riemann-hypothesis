module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleOfRankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal, Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisAlt

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmpty\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow\nimport Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleOfRankOneUnitary\nimport Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted\nimport Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul\nimport Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace UpperTheory.GalN

open GlobalTheory.ParLawsBare GlobalTheory.RowTie GlobalTheory.NPin Polynomial

def TempCSDo (D : D7) : Prop := AllCuspidalOpenBound D.nd D.naut

theorem bareTemp (hP : PrN) {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {rep Rw}
    (X : ParIn hL D cf rep Rw) : Formalism.MainNotions.SumRepresentations.adm7 D :=
  GlobalTheory.RowTie.admissible_of_rank_one_unitary D X.T (rankOneUnitary X.T X.cg X.chr)
    (fun a π ha hc hr w => rankTwo hP.what₂.fin hP.what₂.temp hP.what₂.clo X.T X.cg a π ha hc hr w)

theorem parLawsBare : type_of% @GlobalTheory.ParLawsBare.main :=
  _root_.GlobalTheory.ParLawsBare.main

end UpperTheory.GalN
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal =====

-- ===== clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisAlt =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisAlt", "h": "module\n\npublic import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified\npublic import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
namespace GlobalTheory.AdmIface
theorem main_alt_alt : ∀ D : D7, (Formalism.MainNotions.SumRepresentations.adm1 D → ∀ i, BCEx D.nd D.naut i) ∧ (Formalism.MainNotions.SumRepresentations.adm5 D → ChebSplit D.nd ∧ GlobalTheory.RowCopy.IsobaricCuspidalStrongMultiplicityOne D.nd D.naut ∧ GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut) ∧ (Formalism.MainNotions.SumRepresentations.Conclusion42 D → ∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i) ∧ (_root_.Formalism.MainNotions.SumRepresentations.adm7_alt D ↔ _root_.UpperTheory.GalN.TempCSDo D) ∧ (Formalism.MainNotions.SumRepresentations.adm3 D ↔ ∀ i, GlobalTheory.ThetaExh.SplitLift D.nd D.naut i) ∧ (Formalism.MainNotions.SumRepresentations.adm8 D ↔ Rows.IsotInternal D.what₂) := by
  intro D
  refine ⟨?_, ?_, ?_, Iff.rfl, ?_, Iff.rfl⟩
  · intro h i
    exact h i
  · rintro ⟨h1, h2, h3, -⟩
    refine ⟨?_, h1, h2⟩
    intro S
    rw [dense_iff_closure_eq]
    have := h3 (S : Set (PlE D.host)) S.finite_toSet
    simpa only [Finset.mem_coe] using this
  · intro h i σ P hP
    have hne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
      intro h0
      apply hP.1
      rw [h0, Submodule.map_bot]
    obtain ⟨-, ⟨Sig, hS, hB⟩, -⟩ := h i σ hne
    exact ⟨Sig, hS, hB P hP⟩
  · constructor
    · intro h i σ P hP w hw
      exact h i σ P hP w hw
    · intro h i σ P hP w hw
      exact h i σ P hP w hw
end GlobalTheory.AdmIface
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisAlt =====
