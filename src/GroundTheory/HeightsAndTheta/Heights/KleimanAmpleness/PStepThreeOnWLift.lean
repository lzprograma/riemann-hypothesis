module

import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWLift
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsClaimSeq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanishCech
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Finset.Functor
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace StepThreeOnWLift

section Forms

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem homogeneousComponent_mul_of_isHomogeneous {σ R : Type*} [CommRing R] {P : MvPolynomial σ R}
    {l : ℕ} (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by
  apply GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away.homogeneousComponent_homog_mul <;> assumption

theorem exists_finset_forms (P : Ideal (Poly k N)) :
    ∃ T : Finset (Poly k N), (∀ h ∈ T, h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e) ∧
      ∀ f ∈ P, ∀ e : ℕ, f.IsHomogeneous e → f ∈ Ideal.span (T : Set (Poly k N)) := by
  classical
  obtain ⟨G0, hG0⟩ := IsNoetherian.noetherian (Ideal.span {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e})
  have hmem : ∀ g ∈ G0, ∃ T : Finset (Poly k N),
      (T : Set (Poly k N)) ⊆ {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e} ∧
        g ∈ Ideal.span (T : Set (Poly k N)) := by
    intro g hg
    have hg' : g ∈ Ideal.span {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e} :=
      hG0 ▸ Submodule.subset_span hg
    exact Submodule.mem_span_finite_of_mem_span hg'
  choose! Tf hTf hgT using hmem
  refine ⟨G0.biUnion Tf, fun h hh => ?_, fun f hf e he => ?_⟩
  · obtain ⟨g, hg, hhg⟩ := Finset.mem_biUnion.mp hh
    exact hTf g hg hhg
  · have h1 : f ∈ Ideal.span {h : Poly k N | h ∈ P ∧ ∃ e : ℕ, h.IsHomogeneous e} :=
      Ideal.subset_span ⟨hf, e, he⟩
    rw [← hG0] at h1
    refine (Submodule.span_le.mpr ?_) h1
    intro g hg
    refine Ideal.span_mono ?_ (hgT g hg)
    intro z hz
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨g, hg, hz⟩)


variable (x) in
def idealGraded (P : Ideal (Poly k N)) : FinGradedSub (S := k) (x := x) Ω where
  piece c := Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ P ∧ f.IsHomogeneous e ∧ (e : ℤ) = c ∧
    z = aeval x f}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span k {z |
      ∃ (f : Poly k N) (e : ℕ), f ∈ P ∧ f.IsHomogeneous e ∧ (e : ℤ) = c + d ∧ z = aeval x f})
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨g, e, hg, hge, rfl, rfl⟩
      exact Submodule.subset_span ⟨f * g, d + e, P.mul_mem_left f hg, hf.mul hge,
        by push_cast; ring, by rw [map_mul, smul_eq_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := by
    classical
    obtain ⟨T, hT, hspan⟩ := exists_finset_forms P
    choose! dg hdg using fun h (hh : h ∈ T) => (hT h hh).2
    refine ⟨T.card, fun j => (dg (T.equivFin.symm j).1 : ℤ), fun j => aeval x (T.equivFin.symm j).1,
      fun j => Submodule.subset_span ⟨_, _, (hT _ (T.equivFin.symm j).2).1,
        hdg _ (T.equivFin.symm j).2, rfl, rfl⟩, fun c => ?_⟩
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, e, hfP, hf, rfl, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_finset'.mp (hspan f hfP e hf)
    have h0 : homogeneousComponent e f = f := by rw [homogeneousComponent_of_mem hf, ite_eq_left rfl]
    have hfe : f = ∑ h : T, homogeneousComponent e (h.1 * a h) := by
      calc f = homogeneousComponent e f := h0.symm
        _ = homogeneousComponent e (∑ h : T, a h • h.1) := by rw [ha]
        _ = ∑ h : T, homogeneousComponent e (h.1 * a h) := by

          rw [map_sum]
          exact Finset.sum_congr rfl fun h _ => by rw [smul_eq_mul, mul_comm]

    rw [SetLike.mem_coe, hfe, map_sum]
    refine Submodule.sum_mem _ fun h _ => ?_
    rw [homogeneousComponent_mul_of_isHomogeneous (hdg h.1 h.2)]
    split_ifs with hle
    · refine Submodule.subset_span ⟨T.equivFin h, homogeneousComponent (e - dg h.1) (a h), e - dg h.1,
        homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply]
        push_cast [hle]
        ring
      · simp only [Equiv.symm_apply_apply, map_mul, smul_eq_mul]
        ring
    · rw [map_zero]; exact Submodule.zero_mem _

theorem idealGraded_tildeSys (P : Ideal (Poly k N)) : (idealGraded x P).tildeSys 0 = idealSys x P := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hm' : m ∈ Submodule.span k {z | ∃ (f : Poly k N) (e' : ℕ), f ∈ P ∧ f.IsHomogeneous e' ∧
        (e' : ℤ) = a ∧ z = aeval x f} := hm
    show (aeval x s)⁻¹ • m ∈ idealMod (x := x) P I
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ idealMod (x := x) P I)
      ?_ ?_ ?_ ?_ hm'
    · rintro _ ⟨f, e', hfP, hf, he', rfl⟩
      have hee : e' = e := by omega
      subst hee
      exact Submodule.subset_span ⟨f, s, e', hfP, hs, hf, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r ha
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hfP, hs, hf, hse, rfl⟩
    exact Submodule.subset_span ⟨aeval x f, s, e, e, hs, hse,
      Submodule.subset_span ⟨f, e, hfP, hf, rfl, rfl⟩, by simp, by rw [smul_eq_mul, div_eq_inv_mul]⟩

theorem twist_idealSys_eq (Q : SubSystem k x Ω) (P : Ideal (Poly k N)) :
    Q.twist (idealSys x P) = ((idealGraded x P).tildeSys 0).twist Q := by
  rw [idealGraded_tildeSys]
  refine SubSystem.ext_sub fun I => ?_
  rw [SurjectiveClosed.twist_sub_eq_mul, SurjectiveClosed.twist_sub_eq_mul, mul_comm]

theorem piece_le_idealGraded {J P : Ideal (Poly k N)} (hJP : J ≤ P) (Jg : FinGradedSub (S := k) (x := x) Ω)
    (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ J ∧
      f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) :
    ∀ c, Jg.piece c ≤ (idealGraded x P).piece c := by
  intro c
  rw [hJg]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, e, hf, hfe, he, rfl⟩
  exact ⟨f, e, hJP hf, hfe, he, rfl⟩

theorem idealGraded_kill {J : Ideal (Poly k N)} (P : Ideal (Poly k N)) (Jg : FinGradedSub (S := k) (x := x) Ω)
    (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ J ∧
      f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) :
    ∀ (f : Poly k N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ (idealGraded x P).piece a, aeval x f • z ∈ Jg.piece (a + e) := by
  intro f e hf hfe a z hz
  have hz' : z ∈ Submodule.span k {z | ∃ (g : Poly k N) (e' : ℕ), g ∈ P ∧ g.IsHomogeneous e' ∧
      (e' : ℤ) = a ∧ z = aeval x g} := hz
  rw [hJg]
  refine Submodule.span_induction (p := fun z _ => aeval x f • z ∈ Submodule.span k {z |
    ∃ (f : Poly k N) (e'' : ℕ), f ∈ J ∧ f.IsHomogeneous e'' ∧ (e'' : ℤ) = a + e ∧ z = aeval x f})
    ?_ ?_ ?_ ?_ hz'
  · rintro _ ⟨g, e', -, hg, he', rfl⟩
    exact Submodule.subset_span ⟨f * g, e + e', J.mul_mem_right g hf, hfe.mul hg,
      by push_cast; omega, by rw [map_mul, smul_eq_mul]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha

end Forms

section Lift

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem lift_of_subsingleton (Qc K : SubSystem S x Ω) (hKQ : ∀ I, K.sub I ≤ Qc.sub I)
    (hsub : Subsingleton (K.H 1)) (s : Chart x → Ω) (hs : ∀ I, s I ∈ Qc.sub I)
    (hcompat : ∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ K.sub I₂) :
    ∃ t ∈ Qc.secs, ∀ I, t - s I ∈ K.sub I :=
  SurjectiveClosed.lift_of_subsingleton Qc K hKQ hsub s hs hcompat

end Lift

end StepThreeOnWLift


open StepThreeOnWLift in
theorem StepThree.OnW.Lift.proof (hSeq : ClaimSeq.Statement.{u, w}) (hVan : ClaimVanish.Statement.{u, w})
    (hTwo : StepTwo.Statement.{u, w, w}) : StepThree.OnW.Lift.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨Jg, hJg, hseq⟩ := hSeq k Ω N x T
  obtain ⟨cV, hV⟩ := hVan k Ω N x T hK
  have hle := piece_le_idealGraded (P := pp) hpp.1.2 Jg hJg
  obtain ⟨cS, hS⟩ := hTwo k Ω N x T hK Ω (idealGraded x pp) Jg hle (idealGraded_kill pp Jg hJg)
  refine ⟨max cS (cV - T.c₁), fun b c hb hc s hs hcomp => ?_⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hH : Subsingleton ((((T.L.pow (b' + 1)).twist (twistSys k x c)).twist (idealSys x pp)).H 1) := by
    rw [twist_idealSys_eq]
    refine SubSystem.subsingleton_H_one_of_quot _
      ((Jg.tildeSys 0).twist ((T.L.pow (b' + 1)).twist (twistSys k x c)))
      (twist_tildeSys_mono hle _) ?_ (hS (b' + 1) c (le_trans (le_max_left _ _) hc))
    exact SubSystem.subsingleton_H_one_of_smul _ _ T.si T.si_ne (hseq b' c)
      (hV b' (c + T.c₁) (by linarith [le_max_right cS (cV - T.c₁)]))
  exact lift_of_subsingleton _ _ (SurjectiveClosed.twist_idealSys_le _ pp) hH s hs hcomp

end

end GroundTheory.Heights₂.Heights.Kleiman
