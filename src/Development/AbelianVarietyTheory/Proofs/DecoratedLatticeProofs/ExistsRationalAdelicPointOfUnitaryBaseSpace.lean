module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Core.Mi

theorem exists_GQ_of_unitary {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (γ : GL (Fin n) D.host.E)
    (hγ : γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (Matrix.reindex (finCongr hn) (finCongr hn) (HSpace.gram V))) :
    ∃ a : GA D V, a ∈ GQ V ∧
      GlobalTheory.AdForm.finM V hn a =
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧
      ∀ τ, GlobalTheory.AdForm.infM θ V hn a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ := by
  subst hn
  have hγ' : Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1 * HSpace.gram V * γ.1 = HSpace.gram V := hγ
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ ∈
      HR (AF D.host.F) (Formalism.L2.Forms.sigD D) (HSpace.gram V) := by
    change Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) *
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F)) * γ.1.map (inclR (F := D.host.F) (AF D.host.F)) =
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F))
    have e : Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j
      rfl
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
  refine ⟨⟨_, hmem⟩, ⟨γ, hγ', rfl⟩, ?_, fun τ => ?_⟩
  · ext i j
    rfl
  · ext i j
    exact (hθ τ).1 (γ.1 i j)

theorem exists_GQ_of_unitary0 : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ γ : GL (Fin (D.R.N 0)) D.host.E, γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ a : GA D (D.sp.X 0), a ∈ GQ (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧ ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ :=
  fun D θ hθ γ hγ => exists_GQ_of_unitary θ hθ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) γ hγ

end GlobalTheory.Core.Mi
