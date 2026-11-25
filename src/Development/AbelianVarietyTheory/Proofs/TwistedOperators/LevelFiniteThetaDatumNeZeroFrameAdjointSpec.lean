module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct

namespace GlobalTheory.FinZeta

theorem levDatum_ne_zero_spec {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO S T) :
    levDatum S T βS βT LT Q m e x ≠ 0 → IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ (∀ PP, PP ∈ LT.Pg ∨ PP ∈ Q → IsUnit (topL T.rank (redM PP (frMapAdj S T βS βT x))).det) ∧ ∃ a : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1), (∀ PP : ↥LT.Pg, ((a PP : GL (Fin T.rank) (kP PP.1)) : Matrix (Fin T.rank) (Fin T.rank) (kP PP.1)) = topL T.rank (redM PP.1 (frMapAdj S T βS βT x))) ∧ (∀ PP : ↥LT.Pg, a PP ∈ blockTri (blkOf LT.r LT.t)) ∧ (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H := by
  intro hne
  unfold levDatum at hne
  split_ifs at hne with h0
  · refine ⟨h0.1, h0.2, ?_⟩
    have hG : omegaG LT m (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := left_ne_zero_of_mul hne
    have hQ : omegaQ Q T.rank m (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := right_ne_zero_of_mul hne
    unfold omegaG at hG
    unfold omegaQ at hQ
    split_ifs at hG with hg
    · split_ifs at hQ with hq
      · obtain ⟨a, ha1, ha2, ha3⟩ := hg.2
        refine ⟨?_, a, ha1, ha2, ha3⟩
        rintro PP (hP | hP)
        · rw [← ha1 ⟨PP, hP⟩]
          exact (a ⟨PP, hP⟩).isUnit.map Matrix.detMonoidHom
        · exact (hq PP hP).2
      · exact absurd rfl hQ
    · exact absurd rfl hG
  · exact absurd rfl hne

end GlobalTheory.FinZeta
