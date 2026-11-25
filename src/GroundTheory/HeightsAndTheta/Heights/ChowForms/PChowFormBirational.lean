module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem pderiv_aeval_eq_sum {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    {σ τ : Type*} [Fintype σ] (ψ : σ → MvPolynomial τ K) (i : τ) (g : MvPolynomial σ F) :
    pderiv i (aeval ψ g) = ∑ j, aeval ψ (pderiv j g) * pderiv i (ψ j) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add (f := _), add_mul,
      Finset.sum_add_distrib, pderiv_X, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    · refine Finset.sum_congr rfl fun b _ => by ring

theorem pderiv_genSubst {K : Type*} [CommRing K] {n k : ℕ} (ζ c : Fin n → K) (i : Fin k) (m : Fin n)
    (j : Fin k × Fin n) :
    pderiv (i, m) (genSubst ζ c j) =
      (if j = (i, m) then 1 else 0) - (if j.1 = i then C (ζ m) * C (c j.2) else 0) := by
  classical
  obtain ⟨j₁, j₂⟩ := j

  simp only [genSubst, map_sub, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add,
  map_sum, pderiv_X, Pi.single_apply, mul_zero]
  by_cases h : j₁ = i
  · subst h
    simp [Prod.ext_iff, eq_comm, mul_comm]
  · simp [Prod.ext_iff, h]

theorem not_dvd_pderiv_of_pderiv_ne_zero {F σ : Type*} [Field F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hne : pderiv i g ≠ 0) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hlt_aux : ∀ m ∈ (pderiv i g).support, m i < degreeOf i g := by
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    lia
  have hi : 0 < degreeOf i g := by
    obtain ⟨m, hm⟩ := support_nonempty.2 hne
    have := hlt_aux m hm
    lia
  have hlt : degreeOf i (pderiv i g) < degreeOf i g :=
    (degreeOf_lt_iff hi).2 hlt_aux
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  lia

theorem chowFormBirational_of_exists_pderiv_ne_zero (h₁ : IncidenceGeneric.Statement)
    {F : Type} [Field F] {n k : ℕ} {P : Ideal (MvPolynomial (Fin n) F)}
    {g : MvPolynomial (Fin (k + 1) × Fin n) F}
    {c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)}
    (hP : IsProjPrime P) (hg : IsChowForm P (k + 1) g) (hc : ∑ j, c j * genPt P j = 1)
    {l : Fin n} (hl : pderiv (0, l) g ≠ 0) :
    ∃ t : Fin n → F, (∑ l, C (t l) * pderiv (0, l) g) ∉ incIdeal P (k + 1) ∧
      ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) *
            C (∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (t l) * genPt P l) =
          aeval (genSubst (genPt P) c) (∑ l, C (t l) * pderiv (0, l) g) * C (genPt P m) := by
  have := hP.isPrime
  classical
  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (h₁ F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)
  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, ite_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_pderiv_ne_zero hg.1 hl
  · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring

theorem ChowFormBirational.proof (h₁ : IncidenceGeneric.Statement)
    (h₂ : ChowFormMultiHomog.Statement) : ChowFormBirational.Statement := by
  intro F _ _ n k P g c hP hg hc
  classical
  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (k + 1) P g hP hg
  obtain ⟨s, hs⟩ := support_nonempty.2 hg.1
  obtain ⟨l, hl⟩ : ∃ l, 0 < s (0, l) := by
    by_contra hcon
    push Not at hcon
    have hw := congrFun (hhom (mem_support_iff.1 hs)) 0
    have : (Finsupp.weight (groupWeight (k + 1) n) s) 0 = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      obtain ⟨x₁, x₂⟩ := x
      by_cases hx : x₁ = 0
      · subst hx; simp [Nat.le_zero.1 (hcon x₂)]
      · simp [groupWeight, hx]
    lia
  have hne : pderiv (0, l) g ≠ 0 := by
    have hle : Finsupp.single (0, l) 1 ≤ s := Finsupp.single_le_iff.2 (by lia)
    intro h0
    have hcoeff := congrArg (AddMonoidAlgebra.coeff · (s - Finsupp.single (0, l) 1)) h0
    simp only [coeff_pderiv, AddMonoidAlgebra.coeff_zero, tsub_add_cancel_of_le hle] at hcoeff
    exact mul_ne_zero (mem_support_iff.1 hs) (Nat.cast_add_one_ne_zero _) hcoeff
  exact chowFormBirational_of_exists_pderiv_ne_zero h₁ hP hg hc hne

end

end GroundTheory.Heights₂.Heights
