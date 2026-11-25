module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.TcAnti
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

open UpperTheory.V.Z.Sym.Al

private theorem det_mem_Uo (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {g : Matrix.GeneralLinearGroup Unit k} (hg : g ∈ KO k Unit) :
    Matrix.GeneralLinearGroup.det g ∈ UpperTheory.V.Hi.Uo k := by
  obtain ⟨h, rfl⟩ := hg
  show valuation k ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h) : kˣ) : k) = 1
  rw [Matrix.GeneralLinearGroup.map_det]
  exact (Valuation.integer.integers (valuation k)).valuation_unit _

theorem UpperTheory.V.Z.Sym.Al.locSph :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, ∀ u ∈ Hi.Uo k, ψ i u = 1) → ∃ v, v ≠ 0 ∧ ∀ u ∈ KO k (Fin n), prinSeries ψ u v = v := by
  intro k _ _ _ _ n ψ hψ
  have key : ∀ g : Levi k (fun _ : Fin n => Unit), (∀ a, g a ∈ KO k Unit) →
      (MonoidHom.comp (ofChar (torusChar ψ)) (leviTorus k (Fin n)).symm.toMonoidHom) g (1 : ℂ) = 1 := by
    intro g hg
    have hs : (leviTorus k (Fin n)).symm g = fun i => Matrix.GeneralLinearGroup.det (g i) := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ofChar_apply, hs, torusChar_apply]
    rw [Finset.prod_eq_one fun i _ => hψ i _ (det_mem_Uo k (hg i))]
    simp
  obtain ⟨f, hf, h1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (points (Fin n)) key
  refine ⟨f, ?_, fun u hu => GlobalTheory.LGrp.mem_fixed.mp hf u hu⟩
  rintro rfl
  simp at h1
