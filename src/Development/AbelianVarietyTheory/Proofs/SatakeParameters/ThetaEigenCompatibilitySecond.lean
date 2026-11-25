module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
public import Formalism.SatakeDualWeyl.StatementF
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

theorem GlobalTheory.EigInert.heckeFunI_umax_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    ∃ (C : Finset (GAf L n ⧸ Umax L n)) (a : GAf L n ⧸ Umax L n → ℂ) (x : GAf L n ⧸ Umax L n → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n (Umax L n) Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ :=
  GlobalTheory.SatIso.heckeFunI_eq_sum Dv _ h (_root_.GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv (_root_.GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
    (_root_.GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) _ (fun _ _ => Iff.rfl) h hh)

