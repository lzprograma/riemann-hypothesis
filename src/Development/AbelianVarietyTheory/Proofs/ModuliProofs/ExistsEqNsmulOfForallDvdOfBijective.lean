module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Subgroup.Finite

@[expose] public section

namespace GlobalTheory

theorem exists_eq_nsmul_of_forall_dvd_of_bijective {La : Type} [AddCommGroup La]
    (EF : LinearMap.BilinForm ℤ La) (hEF : Function.Bijective EF) (N : ℕ) (hN : 0 < N) (c : La)
    (hc : ∀ x, (N : ℤ) ∣ EF c x) : ∃ b, c = N • b := by
  have _ := hN
  let g : La →ₗ[ℤ] ℤ :=
    { toFun := fun x => EF c x / N
      map_add' := fun x y => by simp only [map_add]; exact Int.add_ediv_of_dvd_left (hc x)
      map_smul' := fun r x => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc r (hc x) }
  obtain ⟨b, hb⟩ := hEF.2 g
  refine ⟨b, hEF.1 <| LinearMap.ext fun x => ?_⟩
  rw [map_nsmul, LinearMap.smul_apply, hb, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hc x)).symm

private theorem card_mul_card_orthogonal_eq_card_of_nondegenerate {Q : Type} [AddCommGroup Q] [Finite Q] (N : ℕ)
    [NeZero N] (B : Q →+ Q →+ ZMod N) (hL : ∀ y, (∀ x, B y x = 0) → y = 0)
    (U : AddSubgroup Q) :
    Nat.card U * Nat.card (⨅ t ∈ U, (B t).ker : AddSubgroup Q) = Nat.card Q := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  set V : AddSubgroup Q := ⨅ t ∈ U, (B t).ker with hV
  have hmemV : ∀ x, x ∈ V ↔ ∀ t ∈ U, B t x = 0 := fun x => by
    simp [hV, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker]
  let e : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  have he : ∀ z, e z = 1 → z = 0 := fun z h =>
    ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one e).symm)
  have hrow : ∀ t : U, ∑ x : Q, e (B t x) = if t = 0 then (Fintype.card Q : ℂ) else 0 := fun t => by
    split_ifs with ht
    · subst ht; simp
    · exact (AddChar.sum_eq_zero_iff_ne_zero (ψ := e.compAddMonoidHom (B t))).mpr fun h =>
        ht <| Subtype.ext <| hL t fun x => he _ (by simpa using DFunLike.congr_fun h x)
  have hcol : ∀ x : Q, ∑ t : U, e (B t x) = if x ∈ V then (Fintype.card U : ℂ) else 0 := fun x => by
    split_ifs with hx
    · have : ∀ t : U, e (B t x) = 1 := fun t => by
        rw [(hmemV x).mp hx t t.2, AddChar.map_zero_eq_one]
      simp [this]
    · simpa using (AddChar.sum_eq_zero_iff_ne_zero
        (ψ := e.compAddMonoidHom ((B.flip x).comp U.subtype))).mpr fun h =>
          hx <| (hmemV x).mpr fun t ht => he _ (by simpa using DFunLike.congr_fun h ⟨t, ht⟩)
  have hA : ∑ t : U, ∑ x : Q, e (B t x) = (Fintype.card Q : ℂ) := by
    rw [Fintype.sum_eq_single 0 (fun t ht => by simp [hrow t, ht])]; simp
  have hB : ∑ t : U, ∑ x : Q, e (B t x) = (Fintype.card V : ℂ) * (Fintype.card U : ℂ) := by
    rw [Finset.sum_comm]; simp_rw [hcol]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1; rw [Fintype.card_subtype]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact_mod_cast (mul_comm _ _).trans (hB.symm.trans hA)

private theorem exists_rel_of_dvd_pairing_of_card_mul_eq {La Q P : Type} [AddCommGroup La] [AddCommGroup Q]
    [Finite Q] (N : ℕ) [NeZero N] (π : La →+ Q) (B : Q →+ Q →+ ZMod N)
    (hπeq : ∀ a a', π a = π a' → ∃ c, a' = a + N • c)
    (hL : ∀ y, (∀ x, B y x = 0) → y = 0) (hR : ∀ x, (∀ y, B y x = 0) → x = 0)
    (E : La → La → ℤ) (hE : ∀ a a', ((E a a' : ℤ) : ZMod N) = B (π a) (π a'))
    (T : Set P) (R : La → P → Prop) (hRinv : ∀ a b p, R a p → R (a + N • b) p)
    (hRfun : ∀ a p p', R a p → R a p' → p = p') (hRsurj : ∀ p, ∃ a, R a p)
    (hcard : Nat.card P * Nat.card T = Nat.card Q)
    (horth : ∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ E a a')
    (a : La) (ha : ∀ a' p', R a' p' → (N : ℤ) ∣ E a a') : ∃ p, R a p := by
  classical
  have hz : ∀ a a', (N : ℤ) ∣ E a a' → B (π a) (π a') = 0 := fun a a' h => by
    rw [← hE]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  set S : Set Q := {q | ∃ a p, R a p ∧ π a = q}
  set ST : Set Q := {q | ∃ a p, R a p ∧ p ∈ T ∧ π a = q}
  set U : AddSubgroup Q := AddSubgroup.closure ST with hUdef
  set V : AddSubgroup Q := ⨅ t ∈ U, (B t).ker with hVdef
  set W : AddSubgroup Q := ⨅ x ∈ V, (B.flip x).ker with hWdef
  have hmemV : ∀ x, x ∈ V ↔ ∀ t ∈ U, B t x = 0 := fun x => by simp [hVdef, AddSubgroup.mem_iInf]
  have hmemW : ∀ y, y ∈ W ↔ ∀ x ∈ V, B y x = 0 := fun y => by simp [hWdef, AddSubgroup.mem_iInf]
  have h1 : Nat.card U * Nat.card V = Nat.card Q :=
    card_mul_card_orthogonal_eq_card_of_nondegenerate N B hL U
  have h2 : Nat.card V * Nat.card W = Nat.card Q :=
    card_mul_card_orthogonal_eq_card_of_nondegenerate N B.flip
      (fun x hx => hR x fun y => by simpa using hx y) V
  have hSV : S ⊆ (V : Set Q) := by
    rintro _ ⟨a', p', hr, rfl⟩
    refine (hmemV _).mpr fun t ht => ?_
    have hle : U ≤ (B.flip (π a')).ker := by
      rw [hUdef, AddSubgroup.closure_le]
      rintro _ ⟨a0, p0, h0, hp0, rfl⟩
      exact hz _ _ (horth a0 p0 a' p' h0 hp0 hr)
    exact hle ht
  have hSTU : ST ⊆ (U : Set Q) := AddSubgroup.subset_closure
  have hUW : U ≤ W := fun t ht => (hmemW t).mpr fun x hx => (hmemV x).mp hx t ht
  have hf_inj : Function.Injective fun p : P => π (hRsurj p).choose := fun p p' h => by
    obtain ⟨c, hc⟩ := hπeq _ _ h
    exact hRfun _ _ _ (hc ▸ hRinv _ c p (hRsurj p).choose_spec) (hRsurj p').choose_spec
  have hPS : Nat.card P ≤ Nat.card S :=
    Nat.card_le_card_of_injective (fun p => ⟨π (hRsurj p).choose, _, p, (hRsurj p).choose_spec, rfl⟩)
      fun _ _ h => hf_inj (congrArg Subtype.val h)
  have hTST : Nat.card T ≤ Nat.card ST :=
    Nat.card_le_card_of_injective
      (fun p : T => ⟨π (hRsurj p).choose, _, p, (hRsurj p).choose_spec, p.2, rfl⟩)
      fun _ _ h => Subtype.ext (hf_inj (congrArg Subtype.val h))
  have hSVc : Nat.card S ≤ Nat.card V := Nat.card_mono (Set.toFinite _) hSV
  have hSTUc : Nat.card ST ≤ Nat.card U := Nat.card_mono (Set.toFinite _) hSTU
  have hprod_ge : Nat.card V * Nat.card U ≤ Nat.card S * Nat.card ST := by
    rw [mul_comm, h1, ← hcard]; exact Nat.mul_le_mul hPS hTST
  have hSeq : Nat.card S = Nat.card V := by
    have hSTpos : 0 < Nat.card ST := lt_of_lt_of_le
      (Nat.pos_of_ne_zero fun h => Nat.card_pos.ne' (hcard.symm.trans (by rw [h, mul_zero]))) hTST
    by_contra hne
    have hlt := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne hSVc hne) hSTpos)
      (Nat.mul_le_mul_left _ hSTUc)
    lia
  have hSTeq : Nat.card ST = Nat.card U := by
    have hVpos : 0 < Nat.card V := Nat.card_pos
    by_contra hne
    have hlt := Nat.mul_lt_mul_of_pos_left (lt_of_le_of_ne hSTUc hne) hVpos
    rw [hSeq] at hprod_ge; lia
  have hSVset : S = (V : Set Q) :=
    Set.eq_of_subset_of_ncard_le hSV (by rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]; exact hSeq.symm.le)
  have hSTUset : ST = (U : Set Q) :=
    Set.eq_of_subset_of_ncard_le hSTU (by rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]; exact hSTeq.symm.le)
  have hUWeq : U = W := AddSubgroup.eq_of_le_of_card_ge hUW
    (Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans (h1.symm.trans (mul_comm _ _)))).le
  have haW : π a ∈ W := (hmemW _).mpr fun x hx => by
    obtain ⟨a', p', hr, rfl⟩ := hSVset.symm.subset hx
    exact hz _ _ (ha a' p' hr)
  obtain ⟨a0, p0, h0, _, he⟩ := hSTUset.symm.subset (hUWeq ▸ haW)
  obtain ⟨c, hc⟩ := hπeq _ _ he
  exact ⟨p0, hc ▸ hRinv a0 c p0 h0⟩

theorem exists_rel_of_forall_dvd_of_card_mul :
    ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La), Function.Bijective EF → ∀ (N : ℕ), 0 < N → ∀ (P : Type) (T : Set P) (R : La → P → Prop), (∀ a b p, R a p → R (a + N • b) p) → (∀ a p p', R a p → R a p' → p = p') → (∀ p, ∃ a, R a p) → Nat.card P * Nat.card T = N ^ Module.finrank ℤ La → (∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ EF a a') → ∀ a, (∀ a' p', R a' p' → (N : ℤ) ∣ EF a a') → ∃ p, R a p := by
  intro La _ _ _ EF hEF N hN P T R hRinv hRfun hRsurj hcard horth a ha
  classical
  have : NeZero N := ⟨hN.ne'⟩
  let b := Module.Free.chooseBasis ℤ La
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ La) (Module.Free.ChooseBasisIndex ℤ La) (ZMod N) :=
    fun i j => ((EF (b i) (b j) : ℤ) : ZMod N)
  let π : La →+ (Module.Free.ChooseBasisIndex ℤ La → ZMod N) :=
    { toFun := fun a i => ((b.repr a i : ℤ) : ZMod N)
      map_zero' := by ext i; simp
      map_add' := fun _ _ => by ext i; simp }
  let B : (Module.Free.ChooseBasisIndex ℤ La → ZMod N) →+
      (Module.Free.ChooseBasisIndex ℤ La → ZMod N) →+ ZMod N :=
    AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun x => dotProduct (Matrix.vecMul y M) x)
      (fun x x' => dotProduct_add _ _ _))
      (fun y y' => by ext x; simp [Matrix.add_vecMul, add_dotProduct])
  have hE : ∀ a a', ((EF a a' : ℤ) : ZMod N) = B (π a) (π a') := fun a a' => by
    have hZ : EF a a' = ∑ i, ∑ j, b.repr a i * EF (b i) (b j) * b.repr a' j := by
      conv_lhs => rw [← b.sum_repr a, ← b.sum_repr a']
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hZ]
    simp only [B, π, AddMonoidHom.mk'_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMul,
      dotProduct, M, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdiv : ∀ a, (∀ y, B (π a) y = 0) → ∃ c, a = N • c := fun a h =>
    exists_eq_nsmul_of_forall_dvd_of_bijective EF hEF N hN a fun x => by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hE]; exact h _
  have hsurj : ∀ y, ∃ a, π a = y := fun y =>
    ⟨b.equivFun.symm fun i => ((y i).val : ℤ), by
      ext i
      change ((b.repr (b.equivFun.symm _) i : ℤ) : ZMod N) = y i
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]; simp⟩
  have hL : ∀ y, (∀ x, B y x = 0) → y = 0 := fun y hy => by
    obtain ⟨a, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hdiv a hy
    ext i; simp [π]
  have hπeq : ∀ a a', π a = π a' → ∃ c, a' = a + N • c := fun a a' h => by
    obtain ⟨c, hc⟩ := hdiv (a' - a) fun y => by rw [map_sub, h, sub_self, map_zero]; rfl
    exact ⟨c, by rw [← hc]; abel⟩
  have hinj : Function.Injective fun y => Matrix.vecMul y M := fun y y' h =>
    sub_eq_zero.mp <| hL _ fun x => by
      dsimp only at h
      show dotProduct (Matrix.vecMul (y - y') M) x = 0
      rw [Matrix.sub_vecMul, h, sub_self, zero_dotProduct]
  have hR : ∀ x, (∀ y, B y x = 0) → x = 0 := fun x hx => by
    ext i
    obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinj (Pi.single i 1)
    have h0 : dotProduct (Matrix.vecMul y M) x = 0 := hx y
    simpa [hy] using h0
  have hQ : Nat.card (Module.Free.ChooseBasisIndex ℤ La → ZMod N) = N ^ Module.finrank ℤ La := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Module.finrank_eq_card_chooseBasisIndex]
  exact exists_rel_of_dvd_pairing_of_card_mul_eq N π B hπeq hL hR (fun a a' => EF a a') hE T R
    hRinv hRfun hRsurj (hcard.trans hQ.symm) horth a ha

end GlobalTheory
