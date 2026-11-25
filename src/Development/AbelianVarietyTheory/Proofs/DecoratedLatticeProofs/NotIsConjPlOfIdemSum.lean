module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainOnto.FlagAct


variable {D : D7} {c : Com D} {s : PiLocalization₂ D}

theorem not_isConjPl_of_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∀ PP ∈ P, ∀ PP' ∈ P, ¬ Lev.IsConjPl PP PP' := by
  classical
  intro PP hP PP' hP' hc
  obtain ⟨⟨es, hes, he⟩, h0⟩ := h
  have hsum : ∑ x ∈ P ×ˢ P, es x.1 * cA D (es x.2) = 0 := by
      rw [Finset.sum_product, ← h0, he, map_sum, Finset.sum_mul_sum]
  have hidem : ∀ x ∈ P ×ˢ P,
      (es x.1 * cA D (es x.2)) * (es x.1 * cA D (es x.2)) = es x.1 * cA D (es x.2) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hx
    rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]
  have horth : es PP * cA D (es PP') = 0 :=
    GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) (ι := Pl D.host.E × Pl D.host.E)
      (fun n z hn hz => GlobalTheory.PlaceVec.natCast_mul_eq_zero (D := D) n z hn hz) (fun x => es x.1 * cA D (es x.2)) (P ×ˢ P)
      hidem hsum (PP, PP') (Finset.mem_product.2 ⟨hP, hP'⟩)
  have hfw : ∀ x, x ∈ PP.asIdeal → Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    intro x hx
    obtain ⟨c', hc', hcv⟩ := hc x hx
    have e1 : c' = Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext hcv
    rw [← e1]; exact hc'
  have hiff : ∀ x, x ∈ PP.asIdeal ↔ Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    have hle : PP.asIdeal ≤ PP'.asIdeal.comap (Formalism.L2.Col.cO D.host.E) := fun x hx => hfw x hx
    haveI := PP'.isPrime
    have heq := PP.isMaximal.eq_of_le (Ideal.IsPrime.comap (Formalism.L2.Col.cO D.host.E)).ne_top hle
    intro x
    rw [heq]
    exact Ideal.mem_comap
  have hconj := GlobalTheory.MovedIdem.isIdemAt_conj (hes PP' hP') hiff
  have heq : es PP = cA D (es PP') :=
    (GlobalTheory.ExportSeries.idemAt_eq (hes PP hP)).symm.trans (GlobalTheory.ExportSeries.idemAt_eq hconj)
  have hz : es PP = 0 := by
    calc es PP = es PP * es PP := ((hes PP hP).1.1).symm
      _ = es PP * cA D (es PP') := congrArg (es PP * ·) heq
      _ = 0 := horth
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
  have h3 := ((hes PP hP).2 x hx0).1 hxP
  rw [hz, zero_mul, map_zero] at h3
  exact h3 (zero_mem _)

theorem liftsExist_stage {c : Com D} (hc : c.Is) {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) :
    Lev.LiftsExist s.V s.β s.L := by
  obtain ⟨N, hN, -⟩ := hs.base
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  obtain ⟨e, he⟩ := hc.split
  have hnc := not_isConjPl_of_idemSum he
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  refine GlobalTheory.ParahoricLift.liftsExist s.V s.β s.L s.Λ N hN (fun PP hP PP' hP' => ?_) ?_
  · rw [hPg] at hP
    rw [hPg, hQ] at hP'
    rcases hP' with h | h
    · exact hnc PP hP PP' h
    · exact absurd h (Finset.notMem_empty _)
  · rw [hQ]; exact Finset.disjoint_empty_right _

end GlobalTheory.ChainOnto.FlagAct
