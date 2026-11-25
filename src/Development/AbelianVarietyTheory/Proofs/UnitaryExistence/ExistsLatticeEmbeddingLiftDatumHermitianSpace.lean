module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LiftDatumAlternatingFormSignEqOneStatement
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem map_span_eq_latG (D : D7) (V : HSp D) :
    (Submodule.span (𝓞 D.host.E) {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ V.L0, v = a • x}).map
      ((V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) = latG V 1 := by
  rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.2, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, ha, x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, V.frame.equivFun x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨a, ha, y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨a, ha, x, hx, rfl⟩, by simp⟩

theorem exists_iotaOK : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → (∃ ι, IotaOK (Q.Dw j) (D.sp.W j) ι) ∧ (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ (Q.Dw j).q = WeightFamilies.rho D j ∧ 2 * (Q.Dw j).q < D.R.r := by
  intro D Q hP j hj
  obtain ⟨⟨-, hrt, hrt0, -⟩, -, -, hD⟩ := hP
  obtain ⟨hp, hq, φ, ε, hinj, hrange, hiso⟩ := hD j hj
  have hk := D.R.m_add_three_le_k
  obtain ⟨h1, h2⟩ := hj
  refine ⟨?_, ?_, hq, ?_⟩
  · let e := (((D.sp.W j).frame.equivFun : (D.sp.W j).V →ₗ[D.host.E]
      (Fin (D.sp.W j).rank → D.host.E)).restrictScalars (𝓞 D.host.E))
    have hr : LinearMap.range (e ∘ₗ φ) = latG (D.sp.W j) 1 := by
      rw [LinearMap.range_comp, hrange]
      exact map_span_eq_latG D (D.sp.W j)
    have hspan : Submodule.span D.host.E (Set.range φ) = ⊤ := by
      have h := (GlobalTheory.T.adelicElementLattice_full_and_completion D (D.sp.W j) 1).2.1
      rw [← hr] at h
      have hs : ((LinearMap.range (e ∘ₗ φ) : Submodule _ _) : Set (Fin (D.sp.W j).rank → D.host.E)) =
          ((D.sp.W j).frame.equivFun : (D.sp.W j).V →ₗ[D.host.E] (Fin (D.sp.W j).rank → D.host.E)) ''
            Set.range φ := by
        rw [← Set.range_comp]
        rfl
      rw [hs, ← Submodule.map_span] at h
      exact (Submodule.map_eq_top_iff (e := (D.sp.W j).frame.equivFun)).mp h
    have hε : ε = 1 := GlobalTheory.T.liftDatum_alternatingForm_sign_eq_one D Q.H (Q.Dw j) j ⟨h1, h2⟩ hrt hrt0 hp hq φ ε hinj hspan hiso
    refine ⟨e ∘ₗ φ, hrt, hrt0, ⟨(D.sp.W j).frame.equivFun.injective.comp hinj, hr⟩, fun x y => ?_⟩
    have hx : ∀ z, (D.sp.W j).frame.equivFun.symm ((e ∘ₗ φ) z) = φ z := fun z =>
      (D.sp.W j).frame.equivFun.symm_apply_apply (φ z)
    rw [hx, hx, hiso x y, hε]
    simp
  · rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  · rw [hq]
    simp only [Ranks.sigW, Ranks.r]
    omega

end GlobalTheory.Member
