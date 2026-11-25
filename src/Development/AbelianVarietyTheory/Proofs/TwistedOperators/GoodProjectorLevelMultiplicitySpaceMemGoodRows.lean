module

public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
public import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct Pointwise

namespace GlobalTheory.ProjLift

theorem not_isConjPl_of_div {D : D7} (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {w w' : Pl D.host.E}
    (hw : P.Div k w) (hw' : P.Div k' w') : ¬ IsConjPl w w' := by
  intro hc
  have hov : ∀ {j : Fin 2} {u : Pl D.host.E}, P.Div j u → ((D.host.g j : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal := by
    intro j u hu
    have h1 := P.pb_over j
    rw [← hu] at h1
    have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g j : ℕ) : 𝓞 D.host.K) ∈ u.asIdeal := h1
    rwa [map_natCast] at this
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext (hzv.trans ((bridge_star_holds D.R D.host _).trans
      (D.host.conj.apply_symm_apply (y : D.host.E))))
    exact e ▸ hz
  have hmax : (D.host.conj • w.asIdeal).IsMaximal := by
    have := w.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => w.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have heq : D.host.conj • w.asIdeal = w'.asIdeal := hmax.eq_of_le w'.isPrime.ne_top hle
  have hm := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w (hov hw)).2.2.2
    (P.pb k) (P.pb_over k) w' ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w w').2 heq)
  have hg : D.host.g k = D.host.g k' :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w' hm.1).1.symm.trans
      (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k') (D.host.g_prime k') (D.nd.g_split k') w' (hov hw')).1
  obtain rfl : k = k' := by
    have := D.host.g_ne
    fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hg this | exact absurd hg.symm this
  exact hm.2.1 hw hw'

end GlobalTheory.ProjLift

end
