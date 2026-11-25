module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeKeepsAndCommutes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
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
import Mathlib.Tactic.Linter.Style
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

noncomputable section

namespace GlobalTheory.ChainOntoSph

variable {D : D7}


open Classical in
theorem sep_level {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : OffS D c.S P) : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  rintro PP (h | h)
  · rw [hPg] at h
    exact GlobalTheory.HeckeOffLevel.sep_of_offS hP (by unfold Com.S; exact Finset.mem_image.2 ⟨PP, h, rfl⟩)
  · rw [hQ] at h
    exact absurd h (Finset.notMem_empty _)

theorem exists_unif_of_F (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧
      y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  first | exact _root_.GlobalTheory.SphLabelOps.exists_real_unif | exact @_root_.GlobalTheory.SphLabelOps.exists_real_unif | apply _root_.GlobalTheory.SphLabelOps.exists_real_unif <;> assumption

theorem level_spherical_off_S : ∀ D : D7, ForStage D fun c _ s => SphOff (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S ∧
    SphOff (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S ∧
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ Lev.levG s.V s.β s.L,
      ∃ k₁ ∈ Lev.levG s.V s.β s.L, ∃ k₂ ∈ Lev.levG s.V s.β s.L, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂) ∧
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S) ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E,
      (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  intro D c _ j _ s hs
  obtain ⟨N, hB, hNP⟩ := hs.base
  have hoff : ∀ P, OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S := fun P => GlobalTheory.GoodPrimes.offS_iff _ P
  have key := fun P e f (hP : OffS D c.S P) (hi : IsPrimeIdem P e f) =>
    (GlobalTheory.LevSplit.lev_split s.V s.β s.Λ N s.L hB).2 P e f hi (hNP P ((hoff P).1 hP)) (sep_level hs hP)
  have hex := fun P => (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V).2.1 P
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun P e f hP hi => (key P e f hP hi).2.2, hoff, exists_unif_of_F⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    exact ⟨e, f, hi, h1, h2⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    refine ⟨e, f, hi, h1, fun g hg hf => ?_⟩
    show conj (Lev.levChi s.V s.β s.L g) = 1
    rw [h2 g hg hf, map_one]

end GlobalTheory.ChainOntoSph

end
