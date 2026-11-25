module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAEMulMem

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct

namespace GlobalTheory.HostAdeleIso

theorem intAE_mul_mem (D : D7) {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D)
    (hy : y ∈ intAE D) : x * y ∈ intAE D :=
  GlobalTheory.IntegralAdeleProducts.intAE_mul_mem (F := D.host.F) (E := D.host.E) hx hy

theorem mem_intAE_iff_comm (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y ∈
      Formalism.L2.DIV.RInt D.host.F D.host.E := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem r hr =>
      obtain ⟨a, ha, x, rfl⟩ := hr
      have e : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
          (a ⊗ₜ[D.host.F] (x : D.host.E)) =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha
  · intro hw
    let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm
    have key : ∀ z ∈ Formalism.L2.DIV.RInt D.host.F D.host.E, c z ∈ intAE D := by
      intro z hz
      induction hz using Subring.closure_induction with
      | mem r hr =>
        rcases hr with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
        · exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), b, rfl⟩
        · exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | one =>
        rw [map_one]
        exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), 1, rfl⟩
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
      | mul a b _ _ ha hb => rw [map_mul]; exact intAE_mul_mem D ha hb
    have := key _ hw
    rwa [show c (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = y from
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply _] at this

theorem exists_finiteAdele_equiv : ∀ D : D7, ∃ ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E, (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) ∧ (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) ∧ (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (ι (a ⊗ₜ[D.host.F] (1 : D.host.E)) P - algebraMap D.host.E _ (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) := by
  intro D
  obtain ⟨ι, h1, h2, -, h4⟩ :=
    GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv D.host.F D.host.E
  refine ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans ι,
    fun x => h1 x, fun y => (mem_intAE_iff_comm D y).trans (h2 _), fun a k P n h => h4 a k P n h⟩

end GlobalTheory.HostAdeleIso
