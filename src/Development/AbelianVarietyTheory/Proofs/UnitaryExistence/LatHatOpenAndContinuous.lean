module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
  rw [this]
  exact continuous_snd.comp hc

theorem continuous_infPart (D : D7) : Continuous (infPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (infPart D : AE D → _) = fun z => (e z).1 := funext fun z => (he z).1.symm
  rw [this]
  exact continuous_fst.comp hc

theorem continuous_finHom_val (D : D7) (V : HSp D) : Continuous (fun k : GA D V => (finHom V k).1) := by
  have h : Continuous (fun k : GA D V => (matHom V k).1) :=
    Units.continuous_val.comp continuous_subtype_val
  exact h.matrix_map (continuous_finPart D)

theorem latHat_open_and_continuous : ∀ (D : D7) (V : HSp D), (∀ N : ℕ, 0 < N → IsOpen {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E | ∃ y ∈ latHat V, z = N • y}) ∧ Continuous (fun k : GA D V => (finHom V k).1) ∧ Continuous (finPart D) ∧ Continuous (infPart D) := by
  intro D V
  refine ⟨?_, continuous_finHom_val D V, continuous_finPart D, continuous_infPart D⟩
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  rw [h1]
  exact (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E V.rank (latC V) h4).1

end GlobalTheory.Member
