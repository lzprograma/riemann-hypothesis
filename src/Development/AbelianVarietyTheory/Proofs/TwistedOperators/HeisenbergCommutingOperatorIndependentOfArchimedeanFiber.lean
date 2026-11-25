module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FinFibre

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def fin (x : κ → AF F) : κ → Af F := fun i => (x i).2

def mkv (a : κ → Ainf F) (w : κ → Af F) : κ → AF F := fun i => (a i, w i)

def chi (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (w : κ → Af F) : ℂ := GlobalTheory.HeisSchA.finChar ψ (w ⬝ᵥ q)


variable (κ) in
def alg (ψ : AddChar (AF F) ℂ) : Submodule ℂ ((κ → Af F) → ℂ) := Submodule.span ℂ (Set.range (chi (κ := κ) ψ))

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem chi_mul_eq_schr (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (Φ : (κ → AF F) → ℂ) :
    (fun x => chi ψ q (fin x) * Φ x) =
      schr ψ ((GlobalTheory.HeisSchA.mk 0 1 : AF F) • (0 : κ → AF F),
        (GlobalTheory.HeisSchA.mk 0 1 : AF F) • fun i => GlobalTheory.HeisSchA.mk 0 (q i)) Φ := by
  funext x
  simp only [schr, smul_zero, zero_dotProduct, mul_zero, add_zero]
  congr 1
  rw [chi, GlobalTheory.HeisSchA.finChar_apply]
  congr 1
  symm
  refine Prod.ext ?_ ?_
  · change GlobalTheory.HeisSchA.p1 (x ⬝ᵥ _) = 0
    rw [RingHom.map_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    change GlobalTheory.HeisSchA.p1 (x i) * (0 * 0) = 0
    simp
  · change GlobalTheory.HeisSchA.p2 (x ⬝ᵥ _) = _
    rw [RingHom.map_dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (x i).2 * (1 * q i) = (x i).2 * q i
    rw [one_mul]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem comm_alg (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    {C : (κ → Af F) → ℂ} (hC : C ∈ alg κ ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    T (fun x => C (fin x) * Φ x) = fun x => C (fin x) * T Φ x := by
  induction hC using Submodule.span_induction with
  | mem C h =>
    obtain ⟨q, rfl⟩ := h
    have h0 : evI F (GlobalTheory.HeisSchA.mk 0 1 : AF F) = 0 := by
      change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    rw [chi_mul_eq_schr, chi_mul_eq_schr]
    exact hT _ h0 _ _ Φ hΦ
  | zero =>
    have e : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * T Φ x) = 0 := by funext x; simp
    have e' : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * Φ x) = 0 := by funext x; simp
    rw [e, e', map_zero]
  | add C D _ _ hC hD =>
    have e : (fun x : κ → AF F => (C + D) (fin x) * Φ x) =
        (fun x => C (fin x) * Φ x) + fun x => D (fin x) * Φ x := by funext x; simp [add_mul]
    rw [e, map_add (f := _), hC, hD]
    funext x; simp [add_mul]
  | smul a C _ hC =>
    have e : (fun x : κ → AF F => (a • C) (fin x) * Φ x) = a • fun x => C (fin x) * Φ x := by
      funext x; simp [mul_assoc]
    rw [e, map_smul, hC]
    funext x; simp [mul_assoc]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem main (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (hψ : IsStd ψ)
    (hnd : ∀ w : Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1)
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (y : κ → AF F) (hy : ∀ z, At (evI F) z → Φ (y + z) = 0) :
    T Φ y = 0 := by
  apply GlobalTheory.ArchLocality.fibre <;> assumption

end GlobalTheory.FinFibre


open GlobalTheory.FinFibre in
theorem GlobalTheory.FinFibre.fibre_zero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ, T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 :=
  fun ψ T hψ _ hT Φ hΦ y hy => main ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hT Φ hΦ y hy
