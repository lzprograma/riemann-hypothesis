module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetProj

section General

variable {E : Type} [Field E] [NumberField E]

theorem valuation_eq_exp (w : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    w.valuation E (k : E) = WithZero.exp (-ordF w k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log (by simp)]

variable [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem ordSub_conjP (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ w) (detSub p.deco.1.N) = -ordSub w (detSub p.deco.1.N) := by
  have hfull : Submodule.IsFullLattice E p.deco.1.N := by
    letI : Submodule.IsLattice E p.deco.1.N := p.deco.2.lat
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (ptFr p w)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((isFr_ptFr p w _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • ptFr p w (Pi.single i 1) ∈ p.deco.1.N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (p.deco.1.N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  have h := CharValCompare.val_dual (P := w) ⟨p.deco.2.lat, p.deco.2.uni⟩ (isFr_ptFr p w) (isFr_ptFr p (conjPrime₂ w))
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq hfull (isFr_ptFr p w), ordSub_detSub_eq hfull (isFr_ptFr p (conjPrime₂ w))]
  have h' : w.valuation E ((LinearEquiv.det (ptFr p w) : Eˣ) : E) *
      (conjPrime₂ w).valuation E ((LinearEquiv.det (ptFr p (conjPrime₂ w)) : Eˣ) : E) = 1 := h
  rw [valuation_eq_exp, valuation_eq_exp, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at h'
  omega


open Classical in
theorem valued_compAt_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) (p : DecoF E n ST SG Q)
    (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) = WithZero.exp (-(if w ∈ SB then ordSub w (detSub p.deco.1.N)
      else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub p.deco.1.N)).toNat : ℤ))) := by
  have hfull : Submodule.IsFullLattice E p.deco.1.N := by
    letI : Submodule.IsLattice E p.deco.1.N := p.deco.2.lat
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (ptFr p w)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((isFr_ptFr p w _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • ptFr p w (Pi.single i 1) ∈ p.deco.1.N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (p.deco.1.N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  rw [compAt_detIdl SB p.deco.2.lat]
  split_ifs
  · rw [valued_algebraMap, valuation_eq_exp, ordSub_detSub_eq hfull (isFr_ptFr p w)]
  · simp
  · rw [map_pow, valued_algebraMap, valuation_eq_exp, ordF_unif_self, ← WithZero.exp_nsmul]
    simp

theorem valued_compAt_conjP {SB : Finset (HeightOneSpectrum (𝓞 E))} (hs : ∀ P ∈ SB, conjPrime₂ P ∉ SB)
    (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) =
      Valued.v (compAt (conjPrime₂ w) (detIdl SB p.deco.1.N (ptFr p))) * WithZero.exp (-ordSub w (detSub p.deco.1.N)) := by
  rw [valued_compAt_detIdl, valued_compAt_detIdl, ← WithZero.exp_add, WithZero.exp_inj, CharValCompare.conjP_conjP,
    ordSub_conjP]
  by_cases h : w ∈ SB
  · rw [ite_eq_left h, ite_eq_right (hs w h), ite_eq_left h]
    omega
  · rw [ite_eq_right h, ite_eq_right h]
    split_ifs <;> omega

end General

theorem toDtQ_detPt : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E)))
    (h : Q ⊆ SQ) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → toDtQ H h (detPt H SQ p) = detPt H Q p := by
  intro R H n ST SG Q SQ h p hL
  classical
  have hL' := hL.mono h
  have hsub : uSG SG Q ⊆ uSG SG SQ := by
    intro P
    simp only [Finset.mem_union]
    exact Or.imp_right fun h' => h h'
  unfold detPt
  rw [toDtQ_mk]
  symm
  rw [QuotientGroup.eq, inv_mul_eq_div]
  have h0 : ∀ w (a : Ideles H.E), compAt w a ≠ 0 := fun w a => ((Group.isUnit a).map (compAt w)).ne_zero
  refine mem_KDq_of_conj hL' _ (fun w => ?_) fun P hP => ?_
  · rw [map_div, map_div, map_div₀, map_div₀]
    unfold ptIdl
    rw [valued_compAt_conjP hL.split p w, valued_compAt_conjP hL'.split p w, mul_div_mul_right _ _ WithZero.exp_ne_zero]
  · have e1 : compAt P (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, ite_eq_left hP, ite_eq_left (hsub hP)]
    have e2 : compAt (conjPrime₂ P) (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, ite_eq_right (hL.split P (hsub hP)),
        ite_eq_right (hL'.split P hP), CharValCompare.conjP_conjP, ite_eq_left hP, ite_eq_left (hsub hP)]
    have e3 := valued_sigR (host_cmData R H) P ((finAf H.F H.E (ptIdl H SQ p / ptIdl H Q p) : AfE H.F H.E) - 1)
    rw [map_sub (adAt _ _), adAt_finAf, e2, map_one (adAt _ _), sub_self, map_zero, Valuation.zero_iff,
      map_sub (Formalism.UG.sigR _ _), map_one (Formalism.UG.sigR _ _), map_sub (adAt _ _), map_one (adAt _ _), sub_eq_zero] at e3
    rw [e1, e3, div_one, sub_self, map_zero]
    exact zero_lt_one

end GlobalTheory.Mem.Col2.DetProj
