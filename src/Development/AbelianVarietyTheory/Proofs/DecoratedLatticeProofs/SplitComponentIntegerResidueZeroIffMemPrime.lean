module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem residue_pr_int_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ c : 𝓞 D.host.E,
    ∃ h : p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E c)) ∈ 𝒪[k], (residue 𝒪[k] ⟨_, h⟩ = 0 ↔ c ∈ P.asIdeal) := by
  intro D k _ _ _ _ p P hP c
  have h : p.pr (incA D (c : D.host.E)) ∈ 𝒪[k] := GlobalTheory.LocMod.FullLatFrame.pr_int_mem p c
  refine ⟨h, ?_⟩
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hc : c = 0
  · subst hc
    have h0 : (⟨_, h⟩ : 𝒪[k]) = 0 := by
      apply Subtype.ext
      simp
    refine ⟨fun _ => zero_mem _, fun _ hu => ?_⟩
    exact not_isUnit_zero (h0 ▸ hu)
  have hc' : (c : D.host.E) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have hinv : p.pr (incA D (c : D.host.E)) * p.pr (incA D (c : D.host.E)⁻¹) = 1 := by
    rw [← RingHom.map_mul, ← map_mul (incA D), mul_inv_cancel₀ hc', map_one, map_one]
  rw [hP.2 c hc, ← p.sec_pr, ← p.int_iff]
  apply not_congr
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy' : p.pr (incA D (c : D.host.E)) * (y : k) = 1 := congrArg Subtype.val hy
    have hne : p.pr (incA D (c : D.host.E)) ≠ 0 := left_ne_zero_of_mul_eq_one hinv
    have : p.pr (incA D (c : D.host.E)⁻¹) = y := mul_left_cancel₀ hne (hinv.trans hy'.symm)
    rw [this]; exact y.2
  · intro hi
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝒪[k]) (Subtype.ext hinv)

end GlobalTheory.PhiOneVal
