module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TripleWeilTransfer

variable {D : D7}

theorem isThetaFunO_of_mem_algF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (ε : Bool) {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) {Φ : WO M X → ℂ}
    (hΦ : Φ ∈ algF ψ θ ε A B) : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
  | zero => exact GlobalTheory.OrientedHeis.theta_zero
  | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
  | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx

theorem eq_on_theta {ψ : AddChar (AF D.host.F) ℂ} (ε : Bool) {M X : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    {ω ω' : GlobalTheory.Grid.WRep M X} (h : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) (h' : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω')
    (p : GA D M × GA D X) (f : WO M X → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X f) : ω p f = ω' p f := by
  have e := GlobalTheory.WeilUniq.weilDatum_unique D ψ h.std _ X χ χ' _ _ h h' ((GlobalTheory.Grid.ofSgn ε M).symm p.1, p.2) f hf
  simpa [GlobalTheory.Grid.WRep.toSgn] using e

theorem isCoinvMap_congr {θ : InfFam D} {M X : HSp D} {ω ω' : GlobalTheory.Grid.WRep M X} {S : Submodule ℂ (WO M X → ℂ)}
    {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
    {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO M X → ℂ) →ₗ[ℂ] Pi}
    (he : ∀ q, ∀ Φ ∈ S, ω q Φ = ω' q Φ) (h : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω S Pi rf rl p) : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω' S Pi rf rl p := by
  obtain ⟨⟨sM1, sM2⟩, ⟨sX1, sX2⟩, onto, invf, invl, eqf, eql⟩ := h
  refine ⟨⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, ⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, onto,
    fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_, fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_⟩
  · rw [← he _ Φ hΦ]; exact sM1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sM2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact sX1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sX2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact invf g hg Φ hΦ
  · exact invl τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)
  · rw [← he _ Φ hΦ]; exact eqf g hg Φ hΦ
  · exact eql τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)

end GlobalTheory.TripleWeilTransfer

end
