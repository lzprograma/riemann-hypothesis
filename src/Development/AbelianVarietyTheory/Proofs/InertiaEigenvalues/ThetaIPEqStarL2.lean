module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesCartanDoubleCoset
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevelsStatement
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPow, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPowStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndex, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndexStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMulStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOne, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPow =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPow", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLat\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesCartanDoubleCoset\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.LocKerMod.FrameIdx

variable {K : Type} [Field K] {n : ℕ}

def colHom : (Fin n → K) →+ Matrix (Fin n) (Fin 1) K where
  toFun y := fun i _ => y i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colHom_injective : Function.Injective (colHom (K := K) (n := n)) :=
  fun x y h => funext fun i => congrFun (congrFun h i) 0

@[simp] theorem colHom_apply (y : Fin n → K) (i : Fin n) (j : Fin 1) : colHom y i j = y i := rfl

theorem colHom_mulVec (P : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    colHom (P *ᵥ y) = GlobalTheory.SplitIdx.mulL (n := 1) P (colHom y) := by
  ext i j
  simp only [GlobalTheory.SplitIdx.mulL, AddMonoidHom.mk'_apply, colHom_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem mulL_one : GlobalTheory.SplitIdx.mulL (n := 1) (1 : Matrix (Fin n) (Fin n) K) = AddMonoidHom.id _ := by
  ext y : 1
  simp [GlobalTheory.SplitIdx.mulL]

end GlobalTheory.LocKerMod.FrameIdx


open GlobalTheory.LocKerMod.FrameIdx in
theorem GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → GlobalTheory.LocKerMod.idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  intro D T v w h a ha ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ g hg
  set k : GL (Fin T.rank) (w.adicCompletion D.host.E) := k₁ * t * k₂ with hk
  set Lw := (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup with hLw
  set M := GlobalTheory.SplitIdx.intMat D.host.E w T.rank 1 with hM
  let Φ : (Fin T.rank → w.adicCompletion D.host.E) →+ Matrix (Fin T.rank) (Fin 1) (w.adicCompletion D.host.E) :=
    colHom.comp (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1.mulVecLin.toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 : (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x =
        (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ y := colHom_injective hxy
    have e := congrArg (fun z => a.1 *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec] at e
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec] at e
  have hA : Lw.map Φ = M := by
    ext Y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ i j
      have hx' : a.1 *ᵥ ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x) ∈ GlobalTheory.LFun.latAt w (frameLat T) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]; exact hx
      exact (ha _).2 hx' i
    · intro hY
      refine ⟨a.1 *ᵥ (fun i => Y i 0), (ha _).1 (fun i => hY i 0), ?_⟩
      refine Matrix.ext fun i j => ?_
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ (a.1 *ᵥ fun i => Y i 0)) i 0 = Y i 0
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rfl
  have hB : (Lw.map (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).map Φ =
      M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1) := by
    rw [← hA, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    refine AddMonoidHom.ext fun x => ?_
    show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ
        ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ x)) =
      GlobalTheory.SplitIdx.mulL (n := 1) k.1 (colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x))
    rw [← colHom_mulVec, hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  have step1 : GlobalTheory.LocKerMod.idxAt T w h g = (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).relIndex M := by
    unfold GlobalTheory.LocKerMod.idxAt
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hΦ, hB, hA]
  have hinv : (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).map (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) = M := by
    rw [AddSubgroup.map_map, ← GlobalTheory.SplitIdx.LocIndex.mulL_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mulL_one, AddSubgroup.map_id]
  have hinj : Function.Injective (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) := by
    intro x y hxy
    have e := congrArg (GlobalTheory.SplitIdx.mulL (n := 1) k.1) hxy
    simpa [GlobalTheory.SplitIdx.mulL, ← Matrix.mul_assoc, ← Units.val_mul] using e
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have hv : Valued.v (0 : w.adicCompletion D.host.E) = _ := hϖ
    rw [map_zero] at hv
    exact WithZero.coe_ne_zero hv.symm
  have ht' : (t⁻¹).1 = Matrix.diagonal (fun i => ϖ ^ (-d i)) := by
    have e1 : t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
      rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
    calc (t⁻¹).1 = (t⁻¹).1 * (t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i))) := by rw [e1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hkinv : k⁻¹ = k₂⁻¹ * t⁻¹ * k₁⁻¹ := by rw [hk]; group
  rw [step1, ← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hinv, hkinv,
    GlobalTheory.SplitIdx.LocIndex.relIndex_intMat w T.rank 1 ϖ hϖ (fun i => -d i) t⁻¹ ht' k₂⁻¹ (inv_mem hk₂)
      k₁⁻¹ (inv_mem hk₁)]
  simp
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPow =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPowStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPowStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPow\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU


end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPowStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndex =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndex", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.LocKerMod

theorem relIndex_map_of_proj_left {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X)
    (φ P : X →+ X) (M : X →+ Y) (m : Y →+ Y) (hM : ∀ x, M (φ x) = m (M x)) (hK : ∀ x, M x = 0 → P x = 0)
    (hMP : ∀ x, M (P x) = M x) (hPA : ∀ a ∈ A, P a ∈ A) (hφ : ∀ a ∈ A, φ a - P (φ a) = a - P a) :
    (A.map φ).relIndex A = ((A.map M).map m).relIndex (A.map M) := by
  have e1 : (A.map M).map m = (A.map φ).map M := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun x => (hM x).symm
  rw [e1, ← AddSubgroup.relIndex_comap (H := (A.map φ).map M) M A, ← AddSubgroup.inf_relIndex_right (A.map φ),
    ← AddSubgroup.inf_relIndex_right (((A.map φ).map M).comap M)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨z, ⟨y, hy, rfl⟩, hzx⟩, hx⟩
  refine ⟨?_, hx⟩
  have h1 : P (φ y) = P x := by
    have := hK (φ y - x) (by rw [map_sub, hzx, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  have hy' : (x - P x) + P y ∈ A := add_mem (sub_mem hx (hPA x hx)) (hPA y hy)
  have hMy : M ((x - P x) + P y - y) = 0 := by
    rw [map_sub, map_add (f := _), map_sub, hMP, hMP]; abel
  have h2 : P ((x - P x) + P y) = P y := by
    have := hK _ hMy
    rwa [map_sub, sub_eq_zero] at this
  have h3 : P (φ ((x - P x) + P y)) = P (φ y) := by
    have := hK (φ ((x - P x) + P y) - φ y) (by rw [← map_sub, hM, hMy, map_zero])
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨(x - P x) + P y, hy', ?_⟩
  calc φ ((x - P x) + P y) = (φ ((x - P x) + P y) - P (φ ((x - P x) + P y))) + P (φ ((x - P x) + P y)) := by abel
    _ = ((x - P x) + P y - P ((x - P x) + P y)) + P (φ y) := by rw [hφ _ hy', h3]
    _ = x := by rw [h2, h1]; abel

end GlobalTheory.LocKerMod



open GlobalTheory.LFun in
theorem GlobalTheory.LocKerMod.latIndex_embV_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w →
    ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g := by
  intro D T v w h hi g
  let φ : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finMat D.sp.cm.sig T.gram (GlobalTheory.FinZeta.embV T v g)).mulVecLin.toAddMonoidHom
  let P : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun y i => singleAt D.host.F w 1 * y i) fun a b => funext fun i => mul_add _ _ _
  let M : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → w.adicCompletion D.host.E) :=
    AddMonoidHom.mk' (fun y i => compAt D.host.F w (y i)) fun a b => funext fun i => map_add _ _ _
  let m : (Fin T.rank → w.adicCompletion D.host.E) →+ (Fin T.rank → w.adicCompletion D.host.E) :=
    (locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom
  have hcomp : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (x : Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) i,
      compAt D.host.F u (φ x i) = ((locMat D.sp.cm.sig T.gram (rfl : u.under (𝓞 D.host.F) = _)
        (proj D.sp.cm.sig T.gram (u.under (𝓞 D.host.F)) (GlobalTheory.FinZeta.embV T v g))).1 *ᵥ
          fun j => compAt D.host.F u (x j)) i := by
    intro u x i
    rw [← finMat_map_compAt D.sp.cm.sig T.gram rfl]
    exact RingHom.map_mulVec (compAt D.host.F u) _ x i
  have hM : ∀ x, M (φ x) = m (M x) := by
    intro x
    funext i
    have := hcomp w x i
    subst h
    rw [proj_emb_self] at this
    exact this
  have hK : ∀ x, M x = 0 → P x = 0 := by
    intro x hx
    funext i
    have h0 : compAt D.host.F w (x i) = 0 := congrFun hx i
    show singleAt D.host.F w 1 * x i = 0
    rw [singleAt_mul, h0, mul_zero, singleAt_zero]
  have hMP : ∀ x, M (P x) = M x := by
    intro x
    funext i
    show compAt D.host.F w (singleAt D.host.F w 1 * x i) = compAt D.host.F w (x i)
    rw [map_mul, compAt_singleAt, one_mul]
  have hPA : ∀ a ∈ Formalism.L2.NTheta.LamHat T, P a ∈ Formalism.L2.NTheta.LamHat T := by
    intro a ha
    have e : P a = fun i => singleAt D.host.F w (compAt D.host.F w (a i)) := by
      funext i
      show singleAt D.host.F w 1 * a i = _
      rw [singleAt_mul, one_mul]
    rw [e]
    exact singleAt_mem_lamHat (compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice T ▸ ha))
  have hφ : ∀ a ∈ Formalism.L2.NTheta.LamHat T, φ a - P (φ a) = a - P a := by
    intro a _
    funext i
    show φ a i - singleAt D.host.F w 1 * φ a i = a i - singleAt D.host.F w 1 * a i
    refine compAt_ext fun u => ?_
    by_cases e : u = w
    · subst e
      simp only [map_sub, map_mul, compAt_singleAt, one_mul, sub_self]
    · have hu : u.under (𝓞 D.host.F) ≠ v := fun hu => e ((InertChart.under_eq_iff hi u).1 hu)
      simp only [map_sub, map_mul, compAt_singleAt_ne e, zero_mul, sub_zero]
      rw [hcomp u a i, GlobalTheory.FinZeta.embV, proj_emb_ne _ _ hu, map_one, Units.val_one, Matrix.one_mulVec]
  have hLM : (Formalism.L2.NTheta.LamHat T).map M = (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup := by
    ext y
    rw [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      show (fun i => compAt D.host.F w (a i)) ∈ GlobalTheory.LFun.latAt w (frameLat T)
      exact compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice T ▸ ha)
    · intro hy
      refine ⟨_, singleAt_mem_lamHat hy, ?_⟩
      funext i
      exact compAt_singleAt w (y i)
  unfold latIndex idxAt
  rw [relIndex_map_of_proj_left _ φ P M m hM hK hMP hPA hφ, hLM]
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndex =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndexStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndexStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndex\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU


end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndexStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMulStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMulStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqSq\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU


end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMulStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOne =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOne", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLattice\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPowStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexInertPlaceEqLocalIndexStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMulStatement\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND\nimport Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic\nimport Formalism.SatakeDualWeyl.KpqSubgroupCompact\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.Matrix.FiniteDimensional\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.Interval.Finset.Box\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.LocKerMod

end GlobalTheory.LocKerMod
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOne =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2 =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula\npublic import Formalism.LocalToGlobal.IndefiniteReal.LinksStage\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlaceStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevelsStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOne\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevelsStatement\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.GoodModulus

theorem thetaInner_eq_star_l2 {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (x y : WO S T' → ℂ) :
    thetaIP μ 𝓕 x y = star (GlobalTheory.AdelicScalar.l2 μ 𝓕 x y) := by
  unfold thetaIP GlobalTheory.AdelicScalar.l2 Formalism.IndefR.Lift.pet
  show _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext w
  simp [mul_comm]

end GlobalTheory.RawLift.GoodModulus

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2 =====
