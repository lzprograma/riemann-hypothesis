module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLattice
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionSelfDualExistsEqSmulStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OfDualFamilies
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaLine

abbrev sq := @_root_.GlobalTheory.ConjNorm.Line.sq
alias Hf_eq := _root_.GlobalTheory.ConjNorm.Line.Hf_eq
alias im_Hf := _root_.GlobalTheory.ConjNorm.Line.im_Hf
alias sq_smul_left := _root_.GlobalTheory.ConjNorm.Line.sq_smul_left
alias sq_smul_right := _root_.GlobalTheory.ConjNorm.Line.sq_smul_right
alias sq_add_left := _root_.GlobalTheory.ConjNorm.Line.sq_add_left
alias sq_add_right := _root_.GlobalTheory.ConjNorm.Line.sq_add_right
alias sq_self_im := _root_.GlobalTheory.ConjNorm.Line.sq_self_im
alias embV_smul := _root_.GlobalTheory.ConjNorm.Line.embV_smul
alias embV_sum := _root_.GlobalTheory.ConjNorm.Line.embV_sum
alias expand := _root_.GlobalTheory.ConjNorm.Line.expand
alias lam_mul := _root_.GlobalTheory.ConjNorm.Line.lam_mul
alias theta_line := _root_.GlobalTheory.ConjNorm.Line.theta_line

end GlobalTheory.ThetaLine
