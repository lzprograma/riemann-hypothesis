module

public import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
public import GroundTheory.ProfiniteCohomology.CupProducts.Graded
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.ProfiniteCohomology.PoincareDuality.CupPairingEvalPairingCohomologyMap
public import GroundTheory.ProfiniteCohomology.PoincareDuality.DeltaPairing
public import GroundTheory.ProfiniteCohomology.PoincareDuality.Induced
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

universe u

section Helpers

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem injective_cohomologyMap_zero {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (f : A ⟶ B) (hf : Function.Injective f.hom) : Function.Injective (cohomologyMap f 0).hom := by
  intro x y hxy
  have e := fun z => congrArg (fun φ => φ.hom z) (cohomologyMap_zero_comp_H0Iso_hom f)
  have hx := e x
  have hy := e y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx hy
  have h : ((Rep.invariantsFunctor k G).map f).hom ((H0Iso A).hom.hom x) =
      ((Rep.invariantsFunctor k G).map f).hom ((H0Iso A).hom.hom y) := by
    rw [← hx, ← hy, hxy]
  have h' : (H0Iso A).hom.hom x = (H0Iso A).hom.hom y :=
    Subtype.ext (hf (congrArg Subtype.val h))
  rw [← H0Iso_inv_hom_apply A x, ← H0Iso_inv_hom_apply A y, h']

end Helpers

section Naturality

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D] {n : ℕ} {t : cohomology D 2 →+ ZMod n}

theorem dualityMap_δ {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]
    (hS : S.ShortExact) (hT : (dualShortComplex D S).ShortExact) (x : cohomology S.X₃ 0)
    (y : cohomology (dualRep D S.X₁) 1) :
    dualityMap D (rfl : 1 + 1 = 2) t S.X₁ ((δ hS 0 1 rfl).hom x) y =
      -dualityMap D (rfl : 0 + 2 = 2) t S.X₃ x ((δ hT 1 2 rfl).hom y) := by
  rw [dualityMap_apply, dualityMap_apply, ← map_neg]
  congr 1
  have := cupPairing_δ_eq (S := S) (T := dualShortComplex D S) (p := 0) (p' := 1) (q := 1)
    (q' := 2) (n := 2) (evalPairing D S.X₁) (evalPairing D S.X₂) (evalPairing D S.X₃)
    (tensorHom_evalPairing D S.f) (tensorHom_evalPairing D S.g).symm hS hT rfl rfl rfl rfl x y
  have h1 : ((-1 : ULift.{u} ℤ) ^ (0 + 1)) = -1 := by norm_num
  rw [h1, neg_one_smul] at this
  exact this

end Naturality

section AbstractDevissage

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

structure DualityDevissageData (d n : ℕ) [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
    (P : ℕ → Prop) (σ : ℕ → ℤ) where
  H : (M : Rep.{u} (ULift.{u} ℤ) G) → [IsDiscreteRep M] → ℕ → ModuleCat.{u} (ULift.{u} ℤ)
  Hmap : {M N : Rep.{u} (ULift.{u} ℤ) G} → [IsDiscreteRep M] → [IsDiscreteRep N] →
    (M ⟶ N) → (k : ℕ) → H M k ⟶ H N k
  Hδ : {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} → [IsDiscreteRep S.X₁] → [IsDiscreteRep S.X₂] →
    [IsDiscreteRep S.X₃] → S.ShortExact → (k : ℕ) → H S.X₃ k ⟶ H S.X₁ (k + 1)
  duality : {r s : ℕ} → r + s = d → (M : Rep.{u} (ULift.{u} ℤ) G) → [IsDiscreteRep M] → [Finite M] →
    cohomology M r →+ (H (dualRep D M) s →+ ZMod n)
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  hσ : ∀ s, σ s = 1 ∨ σ s = -1
  subsingleton_top : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (H M (d + 1))
  exists_embed : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) →
    ∃ (W : OpenSubgroup G) (J : Type) (_ : Fintype J)
      (i : M ⟶ ⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n)),
      Function.Injective i.hom ∧ ∀ {r s : ℕ} (h : r + s = d), P s →
        Function.Bijective (duality h
          (⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n) :
            Rep.{u} (ULift.{u} ℤ) G))
  Hmap_comp : ∀ {A B C : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (f : A ⟶ B) (g : B ⟶ C) (k : ℕ), Hmap (f ≫ g) k = Hmap f k ≫ Hmap g k
  Hmap_zero : ∀ {A B : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep A] [IsDiscreteRep B] (k : ℕ),
    Hmap (0 : A ⟶ B) k = 0
  exact₃ : ∀ {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
    [IsDiscreteRep S.X₃] (hS : S.ShortExact) (k : ℕ) (y : H S.X₃ k),
    (Hδ hS k).hom y = 0 → ∃ z : H S.X₂ k, (Hmap S.g k).hom z = y
  exact₁ : ∀ {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
    [IsDiscreteRep S.X₃] (hS : S.ShortExact) (k : ℕ) (z : H S.X₁ (k + 1)),
    (Hmap S.f (k + 1)).hom z = 0 → ∃ y : H S.X₃ k, (Hδ hS k).hom y = z
  nsmul_H : ∀ {M : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep M], (∀ m : M, n • m = 0) →
    ∀ (k : ℕ) (x : H M k), n • x = 0
  duality_cohomologyMap : ∀ {r s : ℕ} (h : r + s = d)
    {M N : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep M] [IsDiscreteRep N] [Finite M] [Finite N]
    (f : M ⟶ N) (x : cohomology M r) (y : H (dualRep D N) s),
    duality h N ((cohomologyMap f r).hom x) y = duality h M x ((Hmap (dualMap D f) s).hom y)
  duality_δ : ∀ {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
    [IsDiscreteRep S.X₃] [Finite S.X₁] [Finite S.X₂] [Finite S.X₃] (hS : S.ShortExact)
    (hT : (dualShortComplex D S).ShortExact) {r s : ℕ} (h₁ : r + 1 + s = d) (h₀ : r + (s + 1) = d)
    (_ : P s) (q : cohomology S.X₃ r) (y : H (dualRep D S.X₁) s),
    duality h₁ S.X₁ ((δ hS r (r + 1) rfl).hom q) y =
      σ s • duality h₀ S.X₃ q ((Hδ hT s).hom y)

namespace DualityDevissageData

variable {d n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {P : ℕ → Prop} {σ : ℕ → ℤ} (E : DualityDevissageData d n D P σ)

include E in
theorem finite_D : Finite D :=
  finite_of_nonempty_addEquiv (n := n) E.nonempty_addEquiv

include E in
theorem nsmul_D (x : D) : n • x = 0 :=
  nsmul_eq_zero_of_nonempty_addEquiv E.nonempty_addEquiv x

theorem exists_devissage (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    ∃ (I Q : Rep.{u} (ULift.{u} ℤ) G) (_ : IsDiscreteRep I) (_ : IsDiscreteRep Q) (_ : Finite I)
      (_ : Finite Q) (i : M ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ (∀ x : I, n • x = 0) ∧ (∀ x : Q, n • x = 0) ∧
      ∀ {r s : ℕ} (h : r + s = d), P s → Function.Bijective (E.duality h I) := by
  obtain ⟨W, J, _, i, hi, hφ⟩ := E.exists_embed M hM
  have hnI : ∀ x : ((⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype
      (zmodRep.{u} (W : Subgroup G) n) : Rep.{u} (ULift.{u} ℤ) G) : Type u), n • x = 0 := by
    intro x
    rw [biproduct_eq_sum _ x, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← map_nsmul, nsmul_coind_zmodRep_eq_zero W, map_zero]
  have hmono : Mono i := (Rep.mono_iff_injective i).2 hi
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel i)) hmono
      (inferInstance : Epi (cokernel.π i))
  have hQd : IsDiscreteRep (cokernel i) := isDiscreteRep_X₃_of_shortExact hS
  have hsurj : Function.Surjective (cokernel.π i).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hQf : Finite ((cokernel i : Rep.{u} (ULift.{u} ℤ) G) : Type u) :=
    Finite.of_surjective _ hsurj
  refine ⟨_, cokernel i, inferInstance, hQd, inferInstance, hQf, i, cokernel.π i,
    cokernel.condition i, hS, hnI, fun x => ?_, hφ⟩
  obtain ⟨y, rfl⟩ := hsurj x
  rw [← map_nsmul, hnI, map_zero]

theorem injective_zero (hPd : P d) (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Injective (E.duality (Nat.zero_add d) M) := by
  have := E.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := E.exists_devissage M hM
  have hi : Function.Injective i.hom := (Rep.mono_iff_injective i).1 hS.mono_f
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : E.duality (Nat.zero_add d) I ((cohomologyMap i 0).hom x) = 0 := by
    ext y
    rw [E.duality_cohomologyMap (Nat.zero_add d) i x y, hx]
    rfl
  have h2 : (cohomologyMap i 0).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI (Nat.zero_add d) hPd).1 _ h1
  exact (injective_iff_map_eq_zero _).1 (injective_cohomologyMap_zero i hi) x h2

theorem surjective_zero (hPd : P d) (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (E.duality (Nat.zero_add d) M) := by
  have := E.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := E.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact E.nonempty_addEquiv hS hnI
  have hsurj : Function.Surjective (E.Hmap (dualMap D i) d).hom := by
    intro y
    have : Subsingleton (E.H (dualRep D Q) (d + 1)) :=
      E.subsingleton_top (dualRep D Q) (nsmul_dualRep_eq_zero E.nsmul_D)
    exact E.exact₃ hT d y (Subsingleton.elim _ _)
  intro l
  obtain ⟨v, hv⟩ := (hI (Nat.zero_add d) hPd).2
    (l.comp (E.Hmap (dualMap D i) d).hom.toAddMonoidHom)
  have hpv : (cohomologyMap p 0).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (E.injective_zero hPd Q hnQ)
    ext y
    rw [E.duality_cohomologyMap (Nat.zero_add d) p v y, hv]
    change l ((E.Hmap (dualMap D p) d ≫ E.Hmap (dualMap D i) d).hom y) = 0
    rw [← E.Hmap_comp, ← dualMap_comp, w, dualMap_zero, E.Hmap_zero]
    exact map_zero l
  obtain ⟨m, hm⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 0) v hpv
  refine ⟨m, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := hsurj y
  rw [← E.duality_cohomologyMap (Nat.zero_add d) i m z]
  change E.duality (Nat.zero_add d) I ((cohomologyMap S.f 0).hom m) z = _
  rw [hm, hv]
  rfl

theorem bijective_zero (hPd : P d) (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (E.duality (Nat.zero_add d) M) :=
  ⟨E.injective_zero hPd M hM, E.surjective_zero hPd M hM⟩

theorem injective_succ {r s : ℕ} (h₁ : r + 1 + s = d) (h₀ : r + (s + 1) = d) (hPs : P s)
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (E.duality h₀ M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Injective (E.duality h₁ M) := by
  have := E.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := E.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact E.nonempty_addEquiv hS hnI
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : E.duality h₁ I ((cohomologyMap i (r + 1)).hom x) = 0 := by
    ext y
    rw [E.duality_cohomologyMap h₁ i x y, hx]
    rfl
  have hix : (cohomologyMap i (r + 1)).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI h₁ hPs).1 _ h1
  obtain ⟨q, hq⟩ :=
    (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS r (r + 1) rfl) x hix
  have hker : ((E.Hmap (dualMap D p) (s + 1)).hom.toAddMonoidHom).ker ≤
      (E.duality h₀ Q q).ker := by
    intro z hz
    obtain ⟨y, hy⟩ := E.exact₁ hT s z hz
    rw [AddMonoidHom.mem_ker, ← hy]
    have e := E.duality_δ hS hT h₁ h₀ hPs q y
    change E.duality h₁ M ((δ hS r (r + 1) rfl).hom q) y = _ at e
    rw [hq, hx, AddMonoidHom.zero_apply] at e
    rcases E.hσ s with h | h <;> rw [h] at e <;> simpa using e.symm
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (E.nsmul_H (nsmul_dualRep_eq_zero E.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨v, hv⟩ := (ih I hnI).2 ψ
  have hpv : (cohomologyMap p r).hom v = q := by
    apply (ih Q hnQ).1
    ext z
    rw [E.duality_cohomologyMap h₀ p v z, hv, ← hψ]
    rfl
  rw [← hq, ← hpv]
  exact congrArg (fun F => F.hom v) (comp_δ hS r (r + 1) rfl)

theorem surjective_succ {r s : ℕ} (h₁ : r + 1 + s = d) (h₀ : r + (s + 1) = d) (hPs : P s)
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (E.duality h₀ M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (E.duality h₁ M) := by
  have := E.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := E.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact E.nonempty_addEquiv hS hnI
  intro l
  obtain ⟨v, hv⟩ := (hI h₁ hPs).2 (l.comp (E.Hmap (dualMap D i) s).hom.toAddMonoidHom)
  have hpv : (cohomologyMap p (r + 1)).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (E.injective_succ h₁ h₀ hPs ih Q hnQ)
    ext y
    rw [E.duality_cohomologyMap h₁ p v y, hv]
    change l ((E.Hmap (dualMap D p) s ≫ E.Hmap (dualMap D i) s).hom y) = 0
    rw [← E.Hmap_comp, ← dualMap_comp, w, dualMap_zero, E.Hmap_zero]
    exact map_zero l
  obtain ⟨x', hx'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS (r + 1)) v hpv
  set ν := l - E.duality h₁ M x' with hν
  have hker : ((E.Hδ hT s).hom.toAddMonoidHom).ker ≤ ν.ker := by
    intro y hy
    obtain ⟨z, hz⟩ := E.exact₃ hT s y hy
    rw [AddMonoidHom.mem_ker, ← hz, hν, AddMonoidHom.sub_apply, sub_eq_zero]
    change l ((E.Hmap (dualMap D i) s).hom z) =
      E.duality h₁ M x' ((E.Hmap (dualMap D i) s).hom z)
    rw [← E.duality_cohomologyMap h₁ i x' z]
    change _ = E.duality h₁ I ((cohomologyMap S.f (r + 1)).hom x') z
    rw [hx', hv]
    rfl
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (E.nsmul_H (nsmul_dualRep_eq_zero E.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨q, hq⟩ := (ih Q hnQ).2 ψ
  refine ⟨x' + σ s • (δ hS r (r + 1) rfl).hom q, ?_⟩
  ext y
  have e := E.duality_δ hS hT h₁ h₀ hPs q y
  change E.duality h₁ M ((δ hS r (r + 1) rfl).hom q) y = _ at e
  have hψy : ψ ((E.Hδ hT s).hom y) = ν y := congrArg (fun f => f y) hψ
  have hσσ : ∀ a : ZMod n, σ s • (σ s • a) = a := fun a => by
    rcases E.hσ s with h | h <;> rw [h] <;> simp
  rw [map_add (f := _), map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, e, hq, hσσ]
  change _ + ψ ((E.Hδ hT s).hom y) = l y
  rw [hψy, hν, AddMonoidHom.sub_apply, add_sub_cancel]

theorem bijective_succ {r s : ℕ} (h₁ : r + 1 + s = d) (h₀ : r + (s + 1) = d) (hPs : P s)
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (E.duality h₀ M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (E.duality h₁ M) :=
  ⟨E.injective_succ h₁ h₀ hPs ih M hM, E.surjective_succ h₁ h₀ hPs ih M hM⟩

end DualityDevissageData

end AbstractDevissage

section Core

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

structure GroupDualityHypotheses (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep D]
    (t : cohomology D 2 →+ ZMod n) : Prop where
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  finite_two : ∀ (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Finite (cohomology M 2)
  subsingleton_three : ∀ (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (cohomology M 3)
  bijective_cores : ∀ W : OpenSubgroup Γ,
    Function.Bijective (t.comp (cohomologyCores W D 2).hom.toAddMonoidHom)
  isPerfectPairing : ∀ W : OpenSubgroup Γ,
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n (Rep.res (W : Subgroup Γ).subtype D)
        (nsmul_eq_zero_of_nonempty_addEquiv nonempty_addEquiv)) (show 1 + 1 = 2 from rfl)))
      (t.comp (cohomologyCores W D 2).hom.toAddMonoidHom)

namespace GroupDualityHypotheses

variable {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) Γ} [IsDiscreteRep D]
  {t : cohomology D 2 →+ ZMod n} (H : GroupDualityHypotheses n D t)

def toDevissageData : DualityDevissageData 2 n D (fun s => 1 ≤ s) (fun _ => -1) where
  H M _ k := cohomology M k
  Hmap f k := cohomologyMap f k
  Hδ hS k := δ hS k (k + 1) rfl
  duality h M _ _ := dualityMap D h t M
  nonempty_addEquiv := H.nonempty_addEquiv
  hσ _ := Or.inr rfl
  subsingleton_top := H.subsingleton_three
  exists_embed := by
    intro M _ _ hM
    obtain ⟨W, J, _, i, hi⟩ := exists_injective_biproduct_coind (n := n) M hM
    refine ⟨W, J, inferInstance, i, hi, fun h hs =>
      bijective_dualityMap_biproduct D _ h t fun _ =>
        bijective_dualityMap_coind D H.nonempty_addEquiv t W (H.bijective_cores W)
          (H.isPerfectPairing W) h (by omega)⟩
  Hmap_comp := by intro A B C _ _ _ f g k; exact cohomologyMap_comp f g k
  Hmap_zero := by intro A B _ _ k; exact cohomologyMap_zero k
  exact₃ := by intro S _ _ _ hS k; exact (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hS k (k + 1) rfl)
  exact₁ := by intro S _ _ _ hS k; exact (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS k (k + 1) rfl)
  nsmul_H := by intro M _ hM k; exact nsmul_cohomology_eq_zero _ hM k
  duality_cohomologyMap := by
    intro r s h M N _ _ _ _ f x y
    exact dualityMap_cohomologyMap D h t f x y
  duality_δ := by
    intro S _ _ _ _ _ _ hS hT r s h₁ h₀ hs q y
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 1 := by omega
    simpa using dualityMap_δ (t := t) hS hT q y

include H in
theorem finite_D : Finite D :=
  H.toDevissageData.finite_D

omit [NeZero n] in
include H in
theorem nsmul_D (d : D) : n • d = 0 :=
  nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv d


include H in
theorem exists_devissage (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    ∃ (I Q : Rep.{u} (ULift.{u} ℤ) Γ) (_ : IsDiscreteRep I) (_ : IsDiscreteRep Q) (_ : Finite I)
      (_ : Finite Q) (i : M ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ (∀ x : I, n • x = 0) ∧ (∀ x : Q, n • x = 0) ∧
      Function.Bijective (dualityMap D (rfl : 0 + 2 = 2) t I) ∧
      Function.Bijective (dualityMap D (rfl : 1 + 1 = 2) t I) := by
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.toDevissageData.exists_devissage M hM
  exact ⟨I, Q, inferInstance, inferInstance, inferInstance, inferInstance, i, p, w, hS, hnI, hnQ,
    hI rfl (by norm_num), hI rfl le_rfl⟩

end GroupDualityHypotheses

end Core

section Steps

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) Γ} [IsDiscreteRep D]
  {t : cohomology D 2 →+ ZMod n}

namespace GroupDualityHypotheses

variable (H : GroupDualityHypotheses n D t)


include H in
theorem injective_zero (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Injective (dualityMap D (rfl : 0 + 2 = 2) t M) :=
  H.toDevissageData.injective_zero (by norm_num) M hM


include H in
theorem surjective_zero (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Surjective (dualityMap D (rfl : 0 + 2 = 2) t M) :=
  H.toDevissageData.surjective_zero (by norm_num) M hM

include H in
theorem bijective_zero (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (dualityMap D (rfl : 0 + 2 = 2) t M) :=
  H.toDevissageData.bijective_zero (by norm_num) M hM


include H in
theorem injective_one (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Injective (dualityMap D (rfl : 1 + 1 = 2) t M) :=
  H.toDevissageData.injective_succ (r := 0) (s := 1) rfl rfl le_rfl
    (fun N _ _ hN => H.bijective_zero N hN) M hM


include H in
theorem surjective_one (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Surjective (dualityMap D (rfl : 1 + 1 = 2) t M) :=
  H.toDevissageData.surjective_succ (r := 0) (s := 1) rfl rfl le_rfl
    (fun N _ _ hN => H.bijective_zero N hN) M hM

include H in
theorem bijective_one (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (dualityMap D (rfl : 1 + 1 = 2) t M) :=
  H.toDevissageData.bijective_succ (r := 0) (s := 1) rfl rfl le_rfl
    (fun N _ _ hN => H.bijective_zero N hN) M hM

end GroupDualityHypotheses

end Steps

section Generic

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (D : Rep.{u} k Γ) [IsDiscreteRep D]


omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [IsDiscreteRep D] in
theorem tensorHom_toDualDual_evalPairing (M : Rep.{u} k Γ) :
    (𝟙 (dualRep D M) ⊗ₘ toDualDual D M) ≫ evalPairing D (dualRep D M) =
      (β_ (dualRep D M) M).hom ≫ evalPairing D M := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul f m => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cupPairing_toDualDual (M : Rep.{u} k Γ) [IsDiscreteRep M] [IsDiscreteRep (dualRep D M)]
    [IsDiscreteRep (dualRep D (dualRep D M))] (x : cohomology M 2)
    (y : cohomology (dualRep D M) 0) :
    cupPairing (evalPairing D (dualRep D M)) (rfl : 0 + 2 = 2) y
        ((cohomologyMap (toDualDual D M) 2).hom x) =
      cupPairing (evalPairing D M) (rfl : 2 + 0 = 2) x y := by
  calc cupPairing (evalPairing D (dualRep D M)) (rfl : 0 + 2 = 2) y
        ((cohomologyMap (toDualDual D M) 2).hom x)
      = cupPairing (evalPairing D (dualRep D M)) (rfl : 0 + 2 = 2)
          (cohomologyMap (𝟙 (dualRep D M)) 0 y) (cohomologyMap (toDualDual D M) 2 x) := by
        rw [cohomologyMap_id]
        rfl
    _ = cupPairing ((𝟙 (dualRep D M) ⊗ₘ toDualDual D M) ≫ evalPairing D (dualRep D M))
          (rfl : 0 + 2 = 2) y x := cupPairing_cohomologyMap _ _ _ _ _ _
    _ = cupPairing ((β_ (dualRep D M) M).hom ≫ evalPairing D M) (rfl : 0 + 2 = 2) y x := by
        rw [tensorHom_toDualDual_evalPairing]
    _ = cohomologyMap (evalPairing D M) 2
          (cohomologyMap (β_ (dualRep D M) M).hom 2 (cup (rfl : 0 + 2 = 2) y x)) := by
        rw [cupPairing_apply, cohomologyMap_comp]
        rfl
    _ = cupPairing (evalPairing D M) (rfl : 2 + 0 = 2) x y := by
        rw [cohomologyMap_braiding_cup (rfl : 0 + 2 = 2) (rfl : 2 + 0 = 2) y x, zero_mul, pow_zero,
          one_smul]
        rfl

end Generic

section Two

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) Γ} [IsDiscreteRep D]
  {t : cohomology D 2 →+ ZMod n}


omit [NeZero n] in
theorem dualityMap_two_eq (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    [IsDiscreteRep (dualRep D (dualRep D M))] (x : cohomology M 2)
    (y : cohomology (dualRep D M) 0) :
    dualityMap D (rfl : 2 + 0 = 2) t M x y =
      dualityMap D (rfl : 0 + 2 = 2) t (dualRep D M) y
        ((cohomologyMap (toDualDual D M) 2).hom x) := by
  rw [dualityMap_apply, dualityMap_apply, cupPairing_toDualDual]

namespace GroupDualityHypotheses

variable (H : GroupDualityHypotheses n D t)


include H in
theorem bijective_two (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (dualityMap D (rfl : 2 + 0 = 2) t M) := by
  have := H.finite_D
  have : Finite (cohomology M 2) := H.finite_two M hM
  have hbij := bijective_toDualDual H.nonempty_addEquiv hM
  have : IsDiscreteRep (dualRep D (dualRep D M)) := isDiscreteRep_dualRep _ _
  let e : M ≅ dualRep D (dualRep D M) := Rep.isoOfBijective (toDualDual D M) hbij
  have he1 : ∀ z, (cohomologyMap e.inv 2).hom ((cohomologyMap (toDualDual D M) 2).hom z) = z :=
    fun z => by
      change (cohomologyMap e.hom 2 ≫ cohomologyMap e.inv 2).hom z = z
      rw [← cohomologyMap_comp, e.hom_inv_id, cohomologyMap_id]
      rfl
  have he2 : ∀ z, (cohomologyMap (toDualDual D M) 2).hom ((cohomologyMap e.inv 2).hom z) = z :=
    fun z => by
      change (cohomologyMap e.inv 2 ≫ cohomologyMap e.hom 2).hom z = z
      rw [← cohomologyMap_comp, e.inv_hom_id, cohomologyMap_id]
      rfl
  have h0 := H.bijective_zero (dualRep D M) (nsmul_dualRep_eq_zero H.nsmul_D)
  refine bijective_of_bijective_flip (nsmul_cohomology_eq_zero _ hM 2)
    (bilinAddHom (cupPairing (evalPairing D M) (rfl : 2 + 0 = 2))) t ?_
  let c := (cohomologyMap (toDualDual D M) 2).hom.toAddMonoidHom
  let c' := (cohomologyMap e.inv 2).hom.toAddMonoidHom
  have hpre : Function.Bijective fun χ : cohomology (dualRep D (dualRep D M)) 2 →+ ZMod n =>
      χ.comp c := by
    constructor
    · intro χ χ' h
      ext z
      have := congrArg (fun f : cohomology M 2 →+ ZMod n => f ((c' z))) h
      simpa [c, c', he2] using this
    · intro ξ
      refine ⟨ξ.comp c', ?_⟩
      ext z
      simp [c, c', he1]
  have hfun : (fun y => t.comp ((bilinAddHom (cupPairing (evalPairing D M)
      (rfl : 2 + 0 = 2))).flip y)) =
      fun y => (dualityMap D (rfl : 0 + 2 = 2) t (dualRep D M) y).comp c := by
    funext y
    ext x
    exact dualityMap_two_eq M x y
  rw [hfun]
  exact hpre.comp h0


include H in
theorem bijective_dualityMap (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective (dualityMap D h t M) := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (r = 0 ∧ s = 2) ∨ (r = 1 ∧ s = 1) ∨ (r = 2 ∧ s = 0) := by omega
  · exact H.bijective_zero M hM
  · exact H.bijective_one M hM
  · exact H.bijective_two M hM

end GroupDualityHypotheses

end Two

end GroundTheory.ProfCoh
