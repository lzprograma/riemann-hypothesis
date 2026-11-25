module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerOComponents
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexLocPNeZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexPerDvd
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.LatFin


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.MomT.LatFin.per_lattice_facts : ∀ (X : _root_.Formalism.L2.Col.Fields) (A : _root_.Formalism.L2.Ker.Amb X) (a b : ℕ)
    (N : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E b)),
    A.AA.FG → A.AA ≠ ⊥ → _root_.Formalism.L2.Col.IsSdLat N → _root_.Formalism.L2.Col.IsSdLat N' → (_root_.GlobalTheory.MomT.per A N N').FG ∧
    (∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N') ∧
    (∀ r : 𝓞 X.E, r ≠ 0 → (_root_.GlobalTheory.MomT.smulLat (r : X.E)
      (_root_.GlobalTheory.MomT.per A N N')).toAddSubgroup.relIndex
        (_root_.GlobalTheory.MomT.per A N N').toAddSubgroup ≠ 0) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A.AA =
      _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : _root_.Formalism.L2.Col.HomE X.E a b,
      y ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (_root_.GlobalTheory.MomT.per A N N') ↔
        ∀ v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, y v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := by
  intro X A a b N N' hAfg hA hN hN'
  have full_of_sd {n : ℕ} {L : Submodule (𝓞 X.E) (Sp X.E n)}
      (hL : IsSdLat L) : Submodule.IsFullLattice X.E L :=
    { toIsLattice := hL.1
      span_eq_top := IsUnimodular.span_eq_top hL.2 hStd_isSymm hL.1.fg }
  have hNfull := full_of_sd hN
  have hN'full := full_of_sd hN'
  obtain ⟨hNl, -⟩ := hN
  obtain ⟨hN'l, -⟩ := hN'
  have hfull : _root_.GlobalTheory.ThetaMove.Full (_root_.Formalism.L2.Ker.perO A.AA N N') :=
    _root_.GlobalTheory.ThetaMove.PeriodComp.full A.AA N N' hNl.fg hN'full hA
  have hfg : (_root_.GlobalTheory.MomT.per A N N').FG :=
    _root_.GlobalTheory.ThetaMove.VolumePos.perO_fg hAfg
      (_root_.GlobalTheory.ThetaMove.VolumePos.homO_fg hNl.fg hN'l.fg (by
        let := hNfull
        exact Submodule.IsFullLattice.span_eq_top))
  have hmult : ∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧
      (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N' := by
    intro x
    obtain ⟨n, hn, hx⟩ := hfull x
    refine ⟨n, hn, ?_⟩
    unfold _root_.GlobalTheory.MomT.per
    rw [Nat.cast_smul_eq_nsmul]
    rwa [Nat.cast_smul_eq_nsmul] at hx
  refine ⟨hfg, hmult, ?_, ?_⟩
  · intro r hr
    refine _root_.GlobalTheory.ThetaMove.VolumePos.relIndex_ne_zero ?_ hfg
    intro x
    obtain ⟨n, hn, hx⟩ := hmult ((r : X.E)⁻¹ • x)
    refine ⟨n, hn, ?_⟩
    rw [_root_.GlobalTheory.MomT.mem_smulLat]
    refine ⟨_, hx, ?_⟩
    have hr' : (r : X.E) ≠ 0 := by exact_mod_cast hr
    rw [smul_smul, smul_smul, mul_comm (r : X.E), mul_assoc, mul_inv_cancel₀ hr', mul_one,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · intro P hP y
    unfold _root_.GlobalTheory.MomT.per
    constructor
    · intro hy v hv
      obtain ⟨s, hs, hsy⟩ := (_root_.Formalism.L2.Col.mem_locP P _ y).mp hy
      refine _root_.GlobalTheory.MomT.IdxBound.mem_localization_of_smul_mem P N' hs ?_
      simpa using _root_.GlobalTheory.MomT.IdxBound.per_apply_mem hP hsy hv
    · intro hy
      exact _root_.GlobalTheory.MomT.IdxBound.mem_localization_perO hP hNl.fg fun v hv =>
        hy v (_root_.GlobalTheory.ThetaMove.mem_localization_of_mem P hv)

end GlobalTheory.MomT.LatFin
