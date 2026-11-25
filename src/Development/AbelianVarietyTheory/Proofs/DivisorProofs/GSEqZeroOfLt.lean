module

import Development.WeilBound.ThetaLifts.WeilDomination.FacNeGauss
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified

@[expose] public section

noncomputable section

open ValuativeRel Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

namespace GlobalTheory.GaussNonvanish

section Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rep {c : ℕ} (y : Res k c) : k := ((Quotient.out y : 𝒪[k]) : k)

theorem rep_le_one {c : ℕ} (y : Res k c) : valuation k (rep y) ≤ 1 := (Quotient.out y).2

theorem mk_eq_mk_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) a = Ideal.Quotient.mk _ b ↔
      valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd, ← map_pow]
  rfl

theorem val_pow_lt_one {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) : valuation k (ϖ : k) ^ c < 1 := by
  have h : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  exact pow_lt_one' h (by omega)

theorem val_rep_unit {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) :
    valuation k (rep (y : Res k c)) = 1 := by
  apply _root_.PositivityTheory.ThK.GaussNe.val_rep_unit <;> assumption

theorem rep_ne_zero {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : rep (y : Res k c) ≠ 0 := by
  intro h
  have := val_rep_unit hϖ hc y
  rw [h, map_zero] at this
  exact zero_ne_one this

def uRep {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : kˣ := Units.mk0 _ (rep_ne_zero hϖ hc y)

theorem psi_congr {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y)
    (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1) {a b : k} (h : valuation k (a - b) ≤ 1) : ψl a = ψl b := by
  rw [show a = b + (a - b) by ring, hadd, hO _ h, mul_one]

theorem nu_congr {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν) {a b : kˣ}
    (hb : valuation k (b : k) = 1) (h : valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c) : ν a = ν b := by
  apply _root_.PositivityTheory.ThK.GaussNe.nu_congr <;> assumption

end Generic
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Sums

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def gS (ψl : k → ℂ) (ν : kˣ →* ℂˣ) {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (x : k) : ℂ :=
  ∑ y : (Res k c)ˣ, (((ν (uRep hϖ hc y))⁻¹ : ℂˣ) : ℂ) * ψl (x * rep (y : Res k c) / (ϖ : k) ^ c)

variable {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
  {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
include hadd hO hc

end Sums
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_condLE {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν : kˣ →* ℂˣ) (hν : Continuous fun x : kˣ => (ν x : ℂ)) :
    ∃ e, CondLE ϖ e ν := by
  apply PositivityTheory.ThK.GaussNe.exists_condLE <;> assumption

end Main
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Place

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem val_le_one_iff {F : Type} [Field F] [NumberField F] (v : Pl F) (x : Fv F v) :
    valuation (Fv F v) x ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

end Place
end GlobalTheory.GaussNonvanish
