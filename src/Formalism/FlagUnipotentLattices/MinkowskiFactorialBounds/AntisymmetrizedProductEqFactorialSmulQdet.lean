module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetTensorDecomposition
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.REAL TensorProduct Finset

set_option linter.all false

noncomputable section

namespace Formalism.HermitianLatticeCounting.P

def orderedTermProduct {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ)
    (σ τ : Equiv.Perm (Fin n)) : A :=
  (List.ofFn fun k : Fin n => Tm E (arg k) (σ k) (τ k)).prod

def doublyAntisymmetrizedProduct {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ) : A :=
  ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E arg σ τ)

theorem term_two_by_two_exchange {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x y : ℂ) (p q c d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d - Tm E x p d * Tm E y q c + Tm E x q d * Tm E y p c =
    Tm E y p c * Tm E x q d - Tm E y q c * Tm E x p d - Tm E y p d * Tm E x q c + Tm E y q d * Tm E x p c :=
  _root_.LocalQuantumDet.term_two_by_two_exchange E x y p q c d

theorem list_prod_ofFn_update_adjacent {A : Type} [Ring A] {t : ℕ} (f g : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k) :
    (List.ofFn g).prod = ((List.ofFn f).take i).prod * (g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩) *
      ((List.ofFn f).drop (i + 2)).prod := by
  apply LocalQuantumDet.list_prod_ofFn_update_adjacent <;> assumption

theorem mul_signed_four_sum_mul_eq {A : Type} [Ring A] (L R a1 a2 a3 a4 : A) :
    L * a1 * R - L * a2 * R - L * a3 * R + L * a4 * R = L * (a1 - a2 - a3 + a4) * R := by
  noncomm_ring

theorem orderedProduct_adjacent_swap_identity {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (i : Fin m)
    (arg : Fin (m + 1) → ℂ) (σ τ : Equiv.Perm (Fin (m + 1))) :
    orderedTermProduct E arg σ τ - orderedTermProduct E arg (σ * Equiv.swap i.castSucc i.succ) τ - orderedTermProduct E arg σ (τ * Equiv.swap i.castSucc i.succ)
        + orderedTermProduct E arg (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ) =
    orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) σ τ
        - orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ) τ
        - orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) σ (τ * Equiv.swap i.castSucc i.succ)
        + orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
            (τ * Equiv.swap i.castSucc i.succ) := by
  apply LocalQuantumDet.orderedProduct_adjacent_swap_identity <;> assumption

theorem antisymmetrizedProduct_adjacent_swap {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (i : Fin m)
    (arg : Fin (m + 1) → ℂ) : doublyAntisymmetrizedProduct E (arg ∘ Equiv.swap i.castSucc i.succ) = doublyAntisymmetrizedProduct E arg := by
  apply LocalQuantumDet.antisymmetrizedProduct_adjacent_swap <;> assumption

theorem antisymmetrizedProduct_perm_invariant {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (π : Equiv.Perm (Fin n))
    (arg : Fin n → ℂ) : doublyAntisymmetrizedProduct E (arg ∘ π) = doublyAntisymmetrizedProduct E arg := by
  cases n with
  | zero =>
    have h : arg ∘ π = arg := funext fun k => k.elim0
    rw [h]
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    revert arg
    induction hπ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro arg
      exact antisymmetrizedProduct_adjacent_swap E i arg
    | one =>
      intro arg
      rfl
    | mul x y _ _ hx hy =>
      intro arg
      show doublyAntisymmetrizedProduct E ((arg ∘ x) ∘ y) = _
      rw [hy (arg ∘ x), hx arg]

theorem antisymmetrizedProduct_eq_factorial_smul_qdet {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    doublyAntisymmetrizedProduct E (fun k => u - (k : ℂ)) = (n.factorial : ℂ) • qdet E u := by
  apply LocalQuantumDet.antisymmetrizedProduct_eq_factorial_smul_qdet <;> assumption

theorem term_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (y : ℂ) (a b : Fin n) :
    Tm (fun a b => -E b a) y a b = -Tm E (-y) b a :=
  _root_.LocalQuantumDet.term_neg_transpose E y a b

theorem orderedTermProduct_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ)
    (σ τ : Equiv.Perm (Fin n)) :
    orderedTermProduct (fun a b => -E b a) arg σ τ = (-1) ^ n * orderedTermProduct E (fun k => -arg k) τ σ := by
  simp only [orderedTermProduct]
  have h : (fun k : Fin n => Tm (fun a b => -E b a) (arg k) (σ k) (τ k)) =
      fun k => -(Tm E (-arg k) (τ k) (σ k)) := funext fun k => term_neg_transpose E (arg k) (σ k) (τ k)
  rw [h, show (List.ofFn fun k => -(Tm E (-arg k) (τ k) (σ k))) =
      (List.ofFn fun k => Tm E (-arg k) (τ k) (σ k)).map Neg.neg by rw [List.map_ofFn]; rfl,
    List.prod_map_neg, List.length_ofFn]

theorem antisymmetrizedProduct_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ) :
    doublyAntisymmetrizedProduct (fun a b => -E b a) arg = (-1) ^ n * doublyAntisymmetrizedProduct E (fun k => -arg k) :=
  _root_.LocalQuantumDet.antisymmetrizedProduct_neg_transpose E arg

theorem quantumDet_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (x : ℂ) :
    qdet (fun a b => -E b a) x = ((-1 : ℂ) ^ n) • qdet E ((n : ℂ) - 1 - x) := by
  apply LocalQuantumDet.quantumDet_neg_transpose <;> assumption

end Formalism.HermitianLatticeCounting.P
