module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem continuous_covolOne_integral {D : D7} {m n : ℕ} {X : Type} [TopologicalSpace X] {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (h : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (F : X → Mx D m n → ℂ)
    (hc : Continuous fun p : X × Mx D m n => F p.1 p.2)
    (hF : ∀ x, ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, F x (γ + a) = F x a) :
    Continuous fun x => ∫ a in 𝓕, F x a ∂μ := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  have hi : ∀ x, IntegrableOn (F x) 𝓕 μ := fun x =>
    GlobalTheory.MixModel.covolOne_integrableOn h _ (hc.comp (Continuous.prodMk_right x)) (hF x)
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hc' : Continuous fun p : X × Mx D m n => ‖F p.1 p.2 - F x₀ p.2‖ :=
    (hc.sub (hc.comp (continuous_const.prodMk continuous_snd))).norm
  have hev : ∀ᶠ x in nhds x₀, ∀ a ∈ K, ‖F x a - F x₀ a‖ < ε / 2 := by
    refine hK.eventually_forall_of_forall_eventually fun a _ => ?_
    refine hc'.continuousAt.eventually_lt continuousAt_const ?_
    simpa using hε
  filter_upwards [hev] with x hx
  rw [dist_eq_norm, ← integral_sub (hi x) (hi x₀)]
  have hb : ∀ a, ‖F x a - F x₀ a‖ ≤ ε / 2 := fun a => by
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hF x γ hγ a, ← hF x₀ γ hγ a]
    exact (hx _ ha).le
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)).trans_lt ?_
  rw [measureReal_def, Measure.restrict_apply_univ, h.2.2, ENNReal.toReal_one, mul_one]
  exact half_lt_self hε

theorem swSec_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IntegrableOn (fun w => φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w)) 𝓕 ν ∧ Continuous (swSec A B omh ν 𝓕 φ) := by
  intro D ψ A B χB omh hω ν 𝓕 hν φ hφ
  refine ⟨GlobalTheory.ThetaMean.integrableOn_lagr hν hφ, ?_⟩
  have hj := GlobalTheory.Unf.jointCont_all D ψ _ _ _ _ omh hω φ hφ
  exact continuous_covolOne_integral hν (fun g w => omh (g, 1) φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w))
    (hj.comp ((continuous_fst.prodMk continuous_const).prodMk (GlobalTheory.ThetaMean.continuous_lagr.comp continuous_snd)))
    (fun g => GlobalTheory.ThetaMean.periodic_lagr (hω.om_pres _ _ hφ))

end GlobalTheory.Core.Rk.IP
