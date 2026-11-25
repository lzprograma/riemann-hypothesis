module

public import Formalism.LocalToGlobal.Columns.SmulMemTrpSet
public import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LogVandermondeBounds.FinrankFiberSumZero

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.LogVandermondeBounds

section G3

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K)

theorem localization_le_of_le_localization {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (w : HeightOneSpectrum (𝓞 K))
    {A B : Submodule (𝓞 K) W} (h : A ≤ localization₂ w.asIdeal B) : localization₂ w.asIdeal A ≤ localization₂ w.asIdeal B := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hy⟩ := h hx
  exact ⟨t * s, Submonoid.mul_mem _ ht hs, by rw [mul_smul]; exact hy⟩

theorem tauLat_le_locP (w : HeightOneSpectrum (𝓞 K)) (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ x ∈ L, ∃ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∉ w.asIdeal ∧ s • x ∈ L') :
    tauLat emb τ L ≤ localization₂ w.asIdeal (tauLat emb τ L') := by
  unfold tauLat
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hsx⟩ := h x hx
  refine ⟨RingOfIntegers.mapRingHom (emb τ) s, hs, ?_⟩
  have e : (RingOfIntegers.mapRingHom (emb τ) s) • (fun a : Fin n => emb τ (x a)) =
      fun a : Fin n => emb τ ((s • x) a) := by
    funext a
    rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl
  change (RingOfIntegers.mapRingHom (emb τ) s) • (fun a : Fin n => emb τ (x a)) ∈ _
  rw [e]
  exact Submodule.subset_span ⟨s • x, hsx, rfl⟩

end G3

section G2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

variable {d : Deco E n ST SG} {a : 𝓞 E}

theorem Deco.Ok.locP_Lsh (hd : d.Ok) (ha : SepElt ST a) (Q : ST) :
    localization₂ Q.1.asIdeal d.Lsh = localization₂ Q.1.asIdeal d.N :=
  le_antisymm (localization_le_of_smul_mem (ha.off Q) fun _ hx => hd.smul_Lsh_mem_N ha.conj hx)
    (localization_le_of_smul_mem (one_notMem Q.1) fun x hx => by rw [one_smul]; exact hd.N_le_Lsh hx)

theorem Deco.Ok.Lsh_le_at (hd : d.Ok) (ha : SepElt ST a) (Q : ST) : d.Lsh ≤ d.at Q.1 := fun x hx => by
  have h1 : x ∈ localization₂ Q.1.asIdeal d.Lsh := le_locP _ _ hx
  rwa [hd.locP_Lsh ha Q] at h1

theorem Deco.Ok.mem_LshKer (hd : d.Ok) (ha : SepElt ST a) (P : ST) (x : Sp E n) :
    x ∈ d.LshKer P ↔ x ∈ d.Lsh ∧ d.f P x = 0 := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨Submodule.zero_mem _, hd.f_zero P⟩
    | add y z _ _ hy hz =>
      exact ⟨Submodule.add_mem _ hy.1 hz.1, by
        rw [hd.f_add P y (hd.Lsh_le_at ha P hy.1) z (hd.Lsh_le_at ha P hz.1), hy.2, hz.2, add_zero]⟩
    | smul r y _ hy =>
      exact ⟨Submodule.smul_mem _ r hy.1, by
        rw [hd.f_smul P r y (hd.Lsh_le_at ha P hy.1), hy.2, mul_zero]⟩
  · intro hx
    exact Submodule.subset_span hx

theorem Deco.Ok.locP_LshKer_self (hd : d.Ok) (ha : SepElt ST a) (P : ST) :
    localization₂ P.1.asIdeal (d.LshKer P) = localization₂ P.1.asIdeal (d.kerAt P) :=
  le_antisymm
    (localization_le_of_smul_mem (ha.off P) fun x hx => by
      obtain ⟨h1, h2⟩ := (hd.mem_LshKer ha P x).1 hx
      exact (hd.mem_kerAt P _).2 ⟨hd.smul_Lsh_mem_N ha.conj h1, by
        rw [hd.f_smul P a x (hd.Lsh_le_at ha P h1), h2, mul_zero]⟩)
    (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by
      rw [one_smul]
      obtain ⟨h1, h2⟩ := (hd.mem_kerAt P x).1 hx
      exact (hd.mem_LshKer ha P x).2 ⟨hd.N_le_Lsh h1, h2⟩)

theorem Deco.Ok.locP_LshKer_ne (hd : d.Ok) (ha : SepElt ST a) {P Q : ST} (h : Q ≠ P) :
    localization₂ Q.1.asIdeal (d.LshKer P) = localization₂ Q.1.asIdeal d.Lsh := by
  obtain ⟨p, hp, hpQ⟩ := exists_mem_notMem (P := P.1) (Q := Q.1) (fun e => h (Subtype.ext e.symm))
  exact le_antisymm
    (localization_le_of_smul_mem (one_notMem Q.1) fun x hx => by
      rw [one_smul]
      exact ((hd.mem_LshKer ha P x).1 hx).1)
    (localization_le_of_smul_mem hpQ fun x hx => (hd.mem_LshKer ha P _).2 ⟨Submodule.smul_mem _ p hx, by
      rw [hd.f_smul P p x (hd.Lsh_le_at ha P hx), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]⟩)

theorem Deco.Ok.LshKer_lattice (hd : d.Ok) (ha : SepElt ST a) (P : ST) : Submodule.IsLattice E (d.LshKer P) :=
  lattice_between hd.L_lattice hd.Lsh_lattice
    (fun x hx => (hd.mem_LshKer ha P x).2 ⟨hd.L_le_Lsh hx, ((hd.mem_L x).1 hx).2 P⟩)
    (fun x hx => ((hd.mem_LshKer ha P x).1 hx).1)

end G2

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem sepElt_of_ok (hPr : Pr.Ok) (u : Pr.Word) : SepElt (Pr.vT u) (cO X.E (Pr.piT u)) := by
  refine ⟨?_, conj_piT_notMem hPr u⟩
  intro P
  rw [cO_cO]
  exact decoFin_mem_of_mem_divs P.2

end Cols

end Formalism.L2.Col
