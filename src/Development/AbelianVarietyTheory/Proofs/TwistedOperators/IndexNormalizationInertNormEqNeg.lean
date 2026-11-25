module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
namespace GlobalTheory.LamInert

theorem lam_qV_inert : ∀ (D : D7) (lam : ℕ →* ℂ), GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → lam (qV D.host.E w) = -((qV D.host.F v : ℕ) : ℂ) := by
  intro D lam hl v w hw
  have hmap : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = w.asIdeal := hw
  have hfix : ∀ x : 𝓞 D.host.F, GlobalTheory.FinWeil.sgO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := fun x => by
    apply RingOfIntegers.coe_injective
    refine (GlobalTheory.FinWeil.coe_sgO D _).trans ?_
    exact (D.host.conjE_mem_hostF_iff _).1 (by
      change ((x : D.host.F) : D.host.E) ∈ _
      exact (x : D.host.F).2)
  have hstab : ∀ r ∈ w.asIdeal, GlobalTheory.FinWeil.sgO D r ∈ w.asIdeal := by
    rw [← hmap]
    have : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤
        (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal).comap (GlobalTheory.FinWeil.sgO D) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, hfix]
      exact Ideal.mem_map_of_mem _ hx
    exact fun r hr => this hr
  have hfin : Finite (𝓞 D.host.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have h1 := ((hl.2 w.asIdeal w.isMaximal hfin).2 hstab).1
  have hcard : Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = qV D.host.E w := by
    change _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : qV D.host.E w = qV D.host.F v ^ 2 :=
    GlobalTheory.LFun.InertChart.absNorm_eq (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hw
  rw [hcard, hsq] at h1
  rw [hsq, h1]
  congr 1
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.LamInert
