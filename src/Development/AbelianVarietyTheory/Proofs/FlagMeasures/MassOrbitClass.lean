module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMassEqSumFrameClasses
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassOrbit

theorem mass_orbit_class {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d₁ : S.Datum) (Λ₁ : Submodule L.O S.V)
    (h₁ : S.IsTerm d₁ Λ₁) (d : S.Datum) :
    (S.mass d fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • S.Fr d₁ Λ₁) =
      ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ := by
  have act := @GlobalTheory.FrameAct.stabiliser_acts_on_terms F _ _ _ _ _ E _ _ _ L r k S
  have trm := @GlobalTheory.HL.TermBasic.term_basic F _ _ _ _ _ E _ _ _ L r k S
  have vol := (@GlobalTheory.HL.volSt F _ _ _ _ _ E _ _ _ L r k S).2
  have hT : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.IsTerm d (h • Λ) := fun d Λ H h hh => (act d Λ H h hh).1
  have hF : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.Fr d (h • Λ) = h • S.Fr d Λ :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.1
  have hB : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, (S.BBzero d (h • Λ) ↔ S.BBzero d Λ) :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.2.2.2.1
  have hI : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ H => (trm d Λ H).2.2.2.2.2.2.1
  rw [GlobalTheory.HL.mass_eq_sumCls L r k S d _ (by
    rintro h hh Λ H ⟨hb, s, hs, e⟩
    refine ⟨(hB d Λ H h hh).2 hb, h * s, S.St.mul_mem hh hs, ?_⟩
    rw [hF d Λ H h hh, e, mul_smul])]
  set C₁ := S.Fr d₁ Λ₁ with hC
  unfold Frames.sumCls
  rw [tsum_eq_single (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁)]
  · have hrel : (MulAction.orbitRel S.St (Set S.FrP))
        (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out C₁ := Quotient.mk_out C₁
    obtain ⟨⟨h, hh⟩, e⟩ := MulAction.orbitRel_apply.1 hrel
    have e' : (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out = h • C₁ := e.symm
    have hint : S.IsIntCls (h • C₁) := by
      rw [hC, ← hF d₁ Λ₁ h₁ h hh]
      exact hI _ _ (hT _ _ h₁ h hh)
    change (if S.IsIntCls (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out then
      ENNReal.ofReal (S.wC (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out) *
        S.nT d (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out _ else 0) = _
    rw [e', ite_eq_left hint, (vol C₁ (hI _ _ h₁).1).2.2.2 h hh]
    congr 1
    unfold Frames.nT
    congr 1
    have hset : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = h • C₁} =
        (fun Λ : Submodule L.O S.V => h • Λ) '' {Λ | S.IsTerm d Λ ∧ S.BBzero d Λ ∧ S.Fr d Λ = C₁} := by
      ext Λ
      constructor
      · rintro ⟨H, ⟨hb, -⟩, e⟩
        have hi := S.St.inv_mem hh
        refine ⟨h⁻¹ • Λ, ⟨hT _ _ H _ hi, (hB _ _ H _ hi).2 hb, ?_⟩, smul_inv_smul h Λ⟩
        rw [hF _ _ H _ hi, e, inv_smul_smul]
      · rintro ⟨Λ', ⟨H, hb, e⟩, rfl⟩
        have e2 : S.Fr d (h • Λ') = h • C₁ := by rw [hF _ _ H _ hh, e]
        exact ⟨hT _ _ H _ hh, ⟨(hB _ _ H _ hh).2 hb, h, hh, e2⟩, e2⟩
    rw [hset]
    exact (MulAction.injective h).encard_image _
  · intro o ho
    have h0 : S.nT d o.out (fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) = 0 := by
      unfold Frames.nT
      have : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = o.out} = ∅ := by
        ext Λ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, ⟨-, s, hs, e⟩, e2⟩
        apply ho
        rw [← Quotient.out_eq o]
        apply Quotient.sound
        exact MulAction.orbitRel_apply.2 ⟨⟨s, hs⟩, by rw [← e2, e]; rfl⟩
      rw [this]
      simp
    simp only [h0, mul_zero, ite_self]

end GlobalTheory.HL.MassOrbit
