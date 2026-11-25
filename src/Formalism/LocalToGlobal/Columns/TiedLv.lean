module

public import Formalism.LocalToGlobal.Columns.TiedAtT
public import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
public import Formalism.LocalToGlobal.Columns.TiedCls

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

section Pr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {M M' : Submodule (𝓞 E) (Sp E n)} {s t : 𝓞 E}

theorem lv_exists_inv {a : 𝓞 E} (ha : a ∉ P.asIdeal) : ∃ t : 𝓞 E, a * t - 1 ∈ P.asIdeal := by
  haveI := P.isMaximal
  have h0 : Ideal.Quotient.mk P.asIdeal a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk P.asIdeal a)⁻¹
  refine ⟨t, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, ht, mul_inv_cancel₀ h0, sub_self]

end Pr

section Dec

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) {a : 𝓞 E} (ha : SepElt ST a) (P : ST)


include ha in
theorem lv_LshKer_eq : d.1.LshKer P = d.1.L ⊔ P.1.asIdeal • d.1.Lsh := by
  classical
  apply le_antisymm
  · intro z hz
    obtain ⟨h1, h2⟩ := (d.2.mem_LshKer ha P z).1 hz
    obtain ⟨c, hc⟩ := lv_exists_inv P.1 (ha.off P)
    obtain ⟨b, hb⟩ := crtPl ST (fun R => if R = P.1 then c else 0)
    have hbP : b - c ∈ P.1.asIdeal := by
      have := hb P.1 P.2
      rwa [ite_eq_left rfl] at this
    have hbQ : ∀ Q : ST, Q ≠ P → b ∈ Q.1.asIdeal := by
      intro Q hQ
      have := hb Q.1 Q.2
      rwa [ite_eq_right (fun e => hQ (Subtype.ext e)), sub_zero] at this
    have he : a * b - 1 ∈ P.1.asIdeal := by
      have : a * b - 1 = a * (b - c) + (a * c - 1) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hbP) hc
    have hL : (a * b) • z ∈ d.1.L := by
      rw [d.2.mem_L]
      refine ⟨?_, fun Q => ?_⟩
      · rw [mul_comm, mul_smul]
        exact Submodule.smul_mem _ b (d.2.smul_Lsh_mem_N ha.conj h1)
      · rw [d.2.f_smul Q (a * b) z (d.2.Lsh_le_at ha Q h1)]
        by_cases hQ : Q = P
        · subst hQ
          rw [h2, mul_zero]
        · rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ a (hbQ Q hQ)), zero_mul]
    have e : z = (a * b) • z + (-(a * b - 1)) • z := by
      rw [← add_smul]
      have : a * b + -(a * b - 1) = 1 := by ring
      rw [this, one_smul]
    rw [e]
    exact Submodule.add_mem_sup hL (Submodule.smul_mem_smul (neg_mem he) h1)
  · refine sup_le (fun x hx => (d.2.mem_LshKer ha P x).2 ⟨d.2.L_le_Lsh hx, ((d.2.mem_L x).1 hx).2 P⟩) ?_
    rw [Submodule.smul_le]
    intro r hr x hx
    refine (d.2.mem_LshKer ha P _).2 ⟨Submodule.smul_mem _ r hx, ?_⟩
    rw [d.2.f_smul P r x (d.2.Lsh_le_at ha P hx), Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]

include ha in
theorem lv_smul_LshKer_mem {x : Sp E n} (hx : x ∈ d.1.LshKer P) : a • x ∈ d.1.kerAt P := by
  have key : d.1.LshKer P ≤ (d.1.kerAt P).comap (LinearMap.lsmul (𝓞 E) (Sp E n) a) := by
    unfold Deco.LshKer
    rw [Submodule.span_le]
    rintro y ⟨hy, hfy⟩
    show a • y ∈ d.1.kerAt P
    unfold Deco.kerAt
    apply Submodule.subset_span
    refine ⟨d.2.smul_Lsh_mem_N ha.conj hy, ?_⟩
    rw [d.2.f_smul P a y (d.2.Lsh_le_at ha P hy), hfy, mul_zero]
  exact key hx

include ha in
theorem lv_kerAt_le : d.1.kerAt P ≤ d.1.LshKer P := by
  unfold Deco.kerAt Deco.LshKer
  exact Submodule.span_mono fun x hx => ⟨d.2.N_le_Lsh hx.1, hx.2⟩

variable {t : 𝓞 E} (hat : a * t - 1 ∈ P.1.asIdeal)



end Dec

section Comparison₂

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) {n : ℕ} [NeZero n]
  {cls : Type} (s : cls → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs)) (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)


end Comparison₂

section Rec

variable {d : ColDat} (a : ColArgs d)



end Rec

end Formalism.L2.Col
