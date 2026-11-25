module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Tactic.Linter.Style

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

open Cardinal in
private theorem az_card (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 := by
  apply _root_.GlobalTheory.cardinalMk_padicAlgCl_eq_continuum <;> assumption

private noncomputable def azV (l : ℕ) [Fact l.Prime] : ValuationSubring (PadicAlgCl l) :=
  (NormedField.valuation : Valuation (PadicAlgCl l) NNReal).valuationSubring

private theorem mem_azV {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : x ∈ azV l ↔ ‖x‖ ≤ 1 := by
  show ‖x‖₊ ≤ 1 ↔ _
  exact_mod_cast Iff.rfl

private noncomputable def azA {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O →+* azV l :=
  (c.O.val : c.O →+* PadicAlgCl l).codRestrict (azV l) fun x =>
    (mem_azV _).2 ((_root_.GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val))

private theorem azA_loc {l : ℕ} [Fact l.Prime] (c : Coef l) : IsLocalHom (azA c) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx.exists_left_inv
  have hy' : (y : PadicAlgCl l) * (x : PadicAlgCl l) = 1 := congrArg Subtype.val hy
  have h0 : (x : PadicAlgCl l) ≠ 0 := right_ne_zero_of_mul_eq_one hy'
  have hm : (y : PadicAlgCl l) ∈ c.O :=
    (coefSup l).2.2.2 c y ((_root_.GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ((mem_azV _).1 y.2)) ⟨1, x, h0, hy'⟩
  exact IsUnit.of_mul_eq_one_right (⟨y, hm⟩ : c.O) (Subtype.ext hy')

theorem UpperTheory.V.Ws.ambZero :
    ∀ (l : ℕ) [Fact l.Prime], (∃ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e) ∧ Nonempty (PadicAlgCl l ≃+* ℂ) := by
  intro l hl
  refine ⟨⟨{ K := PadicAlgCl l, V := azV l, a := azA, compat := fun _ _ _ _ => rfl, loc := azA_loc, alg := fun x => ?_ },
    RingEquiv.refl _, fun _ _ => rfl, mem_azV⟩, ?_⟩
  · obtain ⟨c, -⟩ := (coefSup l).2.1 1 (by rw [Nat.dvd_one]; exact hl.out.ne_one)
    obtain ⟨c', -, hx⟩ := (coefSup l).2.2.1 c x ((_root_.GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ((mem_azV _).1 x.2))
    refine ⟨c', ⟨x, hx⟩, ?_⟩
    have : azA c' ⟨x, hx⟩ = x := rfl
    rw [this, sub_self]
    exact Ideal.zero_mem _
  · apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
    · rw [az_card]; exact Cardinal.aleph0_lt_continuum
    · exact Cardinal.eq.1 (by rw [az_card, Cardinal.mk_complex])
