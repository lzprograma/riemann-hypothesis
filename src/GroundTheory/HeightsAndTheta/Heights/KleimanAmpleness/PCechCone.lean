module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v

namespace Cech.Cone

section Signs

variable {n : ℕ}

theorem sgn_insert {a b : Fin n} {A : Finset (Fin n)} (ha : a ∉ A) :
    Cech.sgn (insert a A) b = Cech.sgn A b * (if a < b then -1 else 1) := by
  unfold Cech.sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1), pow_succ]
  · rw [mul_one]

theorem sgn_mul_self (A : Finset (Fin n)) (b : Fin n) : Cech.sgn A b * Cech.sgn A b = 1 := by
  unfold Cech.sgn
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem sgn_key {K : Finset (Fin n)} {i₀ j : Fin n} (hi₀ : i₀ ∉ K) (hj : j ∈ K) :
    Cech.sgn K j * Cech.sgn (insert i₀ (K.erase j)) i₀ =
      -(Cech.sgn (insert i₀ K) i₀ * Cech.sgn (insert i₀ K) j) := by
  have hne : j ≠ i₀ := fun e => hi₀ (e ▸ hj)
  have h1 : Cech.sgn (insert i₀ (K.erase j)) i₀ = Cech.sgn (K.erase j) i₀ := by
    rw [sgn_insert (fun hm => hi₀ (Finset.mem_of_mem_erase hm)), ite_eq_right (lt_irrefl _), mul_one]
  have h2 : Cech.sgn (insert i₀ K) i₀ = Cech.sgn K i₀ := by
    rw [sgn_insert hi₀, ite_eq_right (lt_irrefl _), mul_one]
  have h3 := sgn_insert (b := j) hi₀
  have h4 := sgn_insert (b := i₀) (Finset.notMem_erase j K)
  rw [Finset.insert_erase hj] at h4
  rw [h1, h2, h3, h4]
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [ite_eq_left h, ite_eq_right (lt_asymm h)]; ring
  · simp only [ite_eq_right (lt_asymm h), ite_eq_left h]; ring

end Signs

variable {n : ℕ} {U : Finset (Fin n)} {V : Type v} [AddCommGroup V]

def onSet {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (A : Finset (Fin n)) : V :=
  if h : A.card = i + 1 ∧ A ⊆ U then
    s ⟨⟨A, Finset.card_pos.mp (h.1 ▸ Nat.succ_pos i), h.2⟩, h.1⟩
  else 0

theorem onSet_idx {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (I : Cech.Idx U i) :
    onSet s I.1.1 = s I := by
  unfold onSet
  rw [dite_eq_left ⟨I.2, I.1.2.2⟩]

def coneY {i : ℕ} (k : Fin n) (z : Cech.Cochain (fun _ : Cell U => V) (i + 1)) (A : Finset (Fin n)) : V :=
  if k ∈ A then 0 else Cech.sgn (insert k A) k • onSet z (insert k A)

variable {R : Type u} [CommRing R] [Module R V]

theorem d_eq {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (K : Cech.Idx U (i + 1)) :
    Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl

theorem cone_d {i : ℕ} {z : Cech.Cochain (fun _ : Cell U => V) (i + 1)}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) (i + 1) z = 0) {k : Fin n} (hk : k ∈ U)
    (K : Cech.Idx U (i + 1)) :
    ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • coneY k z (K.1.1.erase j) = z K := by
  have hcoc : ∀ L : Finset (Fin n), L ⊆ U → L.card = i + 1 + 1 + 1 →
      ∑ j ∈ L, Cech.sgn L j • onSet z (L.erase j) = 0 := by
    intro L hLU hL
    have h := congrFun hz ⟨⟨L, Finset.card_pos.mp (by omega), hLU⟩, hL⟩
    rw [d_eq] at h
    exact h
  rw [← onSet_idx z K]
  have hK : K.1.1.card = i + 1 + 1 := K.2
  have hKU : K.1.1 ⊆ U := K.1.2.2
  generalize K.1.1 = Kf at hK hKU ⊢
  by_cases h : k ∈ Kf
  · rw [Finset.sum_eq_single k]
    · rw [coneY, ite_eq_right (Finset.notMem_erase k Kf), Finset.insert_erase h, smul_smul,
        sgn_mul_self, one_smul]
    · intro j hj hne
      rw [coneY, ite_eq_left (Finset.mem_erase.mpr ⟨Ne.symm hne, h⟩), smul_zero]
    · exact fun h' => absurd h h'
  · have hc := hcoc (insert k Kf) (Finset.insert_subset hk hKU)
      (by rw [Finset.card_insert_of_notMem h, hK])
    rw [Finset.sum_insert h, Finset.erase_insert h] at hc
    have hb := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hc)
    have hs : ∑ j ∈ Kf, Cech.sgn Kf j • coneY k z (Kf.erase j) =
        -(Cech.sgn (insert k Kf) k •
          ∑ j ∈ Kf, Cech.sgn (insert k Kf) j • onSet z ((insert k Kf).erase j)) := by
      rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : k ≠ j := fun e => h (e ▸ hj)
      have hni : k ∉ Kf.erase j := fun hm => h (Finset.mem_of_mem_erase hm)
      rw [Finset.erase_insert_of_ne hne, coneY, ite_eq_right hni, smul_smul, smul_smul,
        sgn_key h hj, neg_smul]
    rw [hs, hb, smul_neg, neg_neg, smul_smul, sgn_mul_self, one_smul]

theorem onSet_pair {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    {a b : Fin n} (haU : a ∈ U) (hbU : b ∈ U) (hab : a < b) : onSet z {a} = onSet z {b} := by
  have hcard : ({a, b} : Finset (Fin n)).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hz ⟨⟨{a, b}, Finset.insert_nonempty _ _,
    Finset.insert_subset haU (Finset.singleton_subset_iff.mpr hbU)⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin n)), Cech.sgn {a, b} j • onSet z (({a, b} : Finset _).erase j)
    = 0 at h
  have ha : a ∉ ({b} : Finset (Fin n)) := Finset.notMem_singleton.mpr hab.ne
  rw [Finset.sum_pair hab.ne, Finset.erase_insert ha, Finset.erase_insert_of_ne hab.ne,
    Finset.erase_singleton, sgn_insert ha, sgn_insert ha, ite_eq_right (lt_irrefl _), ite_eq_left hab] at h
  have e1 : Cech.sgn ({b} : Finset (Fin n)) a = 1 := by
    simp [Cech.sgn, Finset.filter_singleton, lt_asymm hab]
  have e2 : Cech.sgn ({b} : Finset (Fin n)) b = 1 := by
    simp [Cech.sgn, Finset.filter_singleton]
  rw [e1, e2, insert_empty_eq] at h
  rw [one_mul, one_smul, one_mul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

theorem const {z : Cech.Cochain (fun _ : Cell U => V) 0}
    (hz : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 z = 0)
    (I K : Cech.Idx U 0) : z I = z K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  have haU : a ∈ U := I.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self a)
  have hbU : b ∈ U := K.1.2.2 (by rw [hb]; exact Finset.mem_singleton_self b)
  rw [← onSet_idx z I, ← onSet_idx z K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hz haU hbU h
  · rfl
  · exact (onSet_pair hz hbU haU h).symm

end Cech.Cone


open Cech.Cone in
theorem Cech.Cone.proof : Cech.Cone.Statement.{u, v} := by
  intro R _ V _ _ N J
  refine ⟨?_, ?_, fun z hz I K => const hz I K⟩
  · intro W i₀ hi₀ i z hz hW hJ
    have hWs : ∀ A, onSet z A ∈ W := by
      intro A; unfold onSet; split_ifs
      · exact hW _
      · exact W.zero_mem
    have hJs : ∀ A, ¬ J ⊆ A → onSet z A = 0 := by
      intro A hA; unfold onSet; split_ifs
      · exact hJ _ hA
      · rfl
    refine ⟨fun I => coneY i₀ z I.1.1, fun I => ?_, fun I hI => ?_, ?_⟩
    · change coneY i₀ z I.1.1 ∈ W
      unfold coneY; split_ifs
      · exact W.zero_mem
      · exact zsmul_mem (hWs _) _
    · change coneY i₀ z I.1.1 = 0
      unfold coneY; split_ifs
      · rfl
      · rw [hJs _ fun hs => hI fun x hx =>
          (Finset.mem_insert.mp (hs hx)).resolve_left fun (e : x = i₀) => hi₀ (e ▸ hx), smul_zero]
    · funext K
      rw [d_eq]
      have hY : ∀ j ∈ K.1.1, onSet (fun I => coneY i₀ z I.1.1 :
          Cech.Cochain (fun _ : StdCell N => V) i) (K.1.1.erase j) = coneY i₀ z (K.1.1.erase j) := by
        intro j hj
        unfold onSet
        rw [dite_eq_left ⟨by rw [Finset.card_erase_of_mem hj, K.2]; rfl, Finset.subset_univ _⟩]
      rw [Finset.sum_congr rfl fun j hj => by rw [hY j hj]]
      exact cone_d hz (Finset.mem_univ i₀) K
  · intro hJne i₀ hi₀ z hz hJ
    obtain ⟨j, hj⟩ := hJne
    funext I
    let I₀ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{i₀}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    rw [const hz I I₀]
    exact hJ I₀ fun hs => hi₀ (Finset.mem_singleton.mp (hs hj) ▸ hj)

end

end GroundTheory.Heights₂.Heights.Kleiman
