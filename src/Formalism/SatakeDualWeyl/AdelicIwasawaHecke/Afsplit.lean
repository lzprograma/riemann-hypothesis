module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitC
import Mathlib.Tactic.Lemma

@[expose] public section

noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace Formalism.UG.P
open Formalism.UG

section Lat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem afsplit_mem_stdLat (S : Subring A) (x : n → A) :
    x ∈ stdLat (n := n) (A := A) S ↔ ∀ i, x i ∈ S := by
  constructor
  · intro h i
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp ((Submodule.mem_pi.mp h) i (Set.mem_univ i))
    rw [← hy]
    exact y.2
  · intro h
    exact Submodule.mem_pi.mpr fun i _ => LinearMap.mem_range.mpr ⟨⟨x i, h i⟩, rfl⟩

theorem afsplit_mulVec_mem (S : Subring A) (M : Matrix n n A) (hM : ∀ i j, M i j ∈ S) (x : n → A)
    (hx : ∀ i, x i ∈ S) (i : n) : (M *ᵥ x) i ∈ S := by
  show ∑ j, M i j * x j ∈ S
  exact sum_mem fun j _ => mul_mem (hM i j) (hx j)

theorem afsplit_stab_iff (S : Subring A) (g : GL n A) :
    g ∈ stabGL (stdLat (n := n) (A := A) S) ↔
      (∀ i j, (g : Matrix n n A) i j ∈ S) ∧ (∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ S) := by
  have hmem := fun x : n → A => afsplit_mem_stdLat (n := n) S x
  have hinv : ∀ x : n → A, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ ((g : Matrix n n A) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ x : n → A, (g : Matrix n n A) *ᵥ (((g⁻¹ : GL n A) : Matrix n n A) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hsingle : ∀ j : n, (Pi.single j (1 : A) : n → A) ∈ stdLat (n := n) (A := A) S := by
    intro j
    rw [hmem]
    intro i
    by_cases h : i = j
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h]
      exact S.zero_mem
  have hcol : ∀ (M : Matrix n n A) (i j : n), (M *ᵥ Pi.single j (1 : A)) i = M i j := by
    intro M i j
    first
      | simp
  constructor
  · intro hg
    have hg' : ∀ x : n → A, x ∈ stdLat (n := n) (A := A) S ↔
        (g : Matrix n n A) *ᵥ x ∈ stdLat (n := n) (A := A) S := hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have h1 := ((hmem _).mp ((hg' _).mp (hsingle j))) i
      rwa [hcol] at h1
    · have h1 : (g : Matrix n n A) *ᵥ (((g⁻¹ : GL n A) : Matrix n n A) *ᵥ Pi.single j 1) ∈
          stdLat (n := n) (A := A) S := by
        rw [hinv']
        exact hsingle j
      have h2 := ((hmem _).mp ((hg' _).mpr h1)) i
      rwa [hcol] at h2
  · rintro ⟨h1, h2⟩
    show ∀ x : n → A, x ∈ stdLat (n := n) (A := A) S ↔
      (g : Matrix n n A) *ᵥ x ∈ stdLat (n := n) (A := A) S
    intro x
    rw [hmem, hmem]
    constructor
    · intro hx i
      exact afsplit_mulVec_mem S _ h1 x hx i
    · intro hx i
      have h3 := afsplit_mulVec_mem S _ h2 _ hx i
      rwa [hinv] at h3

theorem afsplit_one_mem (S : Subring A) (i j : n) : (1 : Matrix n n A) i j ∈ S := by
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

end Lat

section Int
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem afsplit_prV_int (x : E ⊗[F] 𝔸ᶠ[F]) (hx : x ∈ tensInt (F := F) 𝔸ᶠ[F] (intOE E) (intAd F)) :
    prV (E := E) v x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := by
  unfold tensInt at hx ⊢
  induction hx using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)
    · exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨(b : 𝔸ᶠ[F]) v, b.2 v⟩, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem afsplit_eps_int : afsplitEps E v ∈ tensInt (F := F) 𝔸ᶠ[F] (intOE E) (intAd F) :=
  Subring.subset_closure
    (Set.mem_union_right _ ⟨⟨afsplitI v 1, afsplitI_mem_intAd v 1 (one_mem _)⟩, rfl⟩)

theorem afsplit_IE_int (x : E ⊗[F] v.adicCompletion F)
    (hx : x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) :
    afsplitIE v x ∈ tensInt (F := F) 𝔸ᶠ[F] (intOE E) (intAd F) := by
  unfold tensInt at hx
  induction hx using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [show afsplitIE v ((a : E) ⊗ₜ[F] 1) = afsplitEps E v * ((a : E) ⊗ₜ[F] 1) from
        afsplit_decomp (E := E) v ((a : E) ⊗ₜ[F] 1)]
      exact mul_mem (afsplit_eps_int v) (Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩))
    · exact Subring.subset_closure
        (Set.mem_union_right _ ⟨⟨afsplitI v b, afsplitI_mem_intAd v b b.2⟩, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | one => exact afsplit_eps_int v
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

variable {n : Type} [Fintype n] [DecidableEq n]

theorem afsplitC_int (M : Matrix n n (E ⊗[F] v.adicCompletion F)) (N : Matrix n n (E ⊗[F] 𝔸ᶠ[F]))
    (hM : ∀ i j, M i j ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring)
    (hN : ∀ i j, N i j ∈ tensInt (F := F) 𝔸ᶠ[F] (intOE E) (intAd F)) (i j : n) :
    afsplitC v M N i j ∈ tensInt (F := F) 𝔸ᶠ[F] (intOE E) (intAd F) := by
  simp only [afsplitC, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact add_mem (afsplit_IE_int v _ (hM i j))
    (mul_mem (sub_mem (one_mem _) (afsplit_eps_int (E := E) v)) (hN i j))

end Int

section Iso
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
  (v : HeightOneSpectrum (𝓞 F))

def afsplitKer : Subgroup (GL n (E ⊗[F] 𝔸ᶠ[F])) := UPts σ J 𝔸ᶠ[F] ⊓ (bc (n := n) (prV (E := E) v)).ker

private lemma prV_sig_lemma_8 (x : E ⊗[F] 𝔸ᶠ[F]) :
    prV (E := E) v (sigR σ 𝔸ᶠ[F] x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) :=
  RingHom.congr_fun (afsplit_prV_comp_sigR σ v) x

theorem afsplit_bc_mem (g : GL n (E ⊗[F] 𝔸ᶠ[F])) (hg : g ∈ UPts σ J 𝔸ᶠ[F]) :
    bc (prV (E := E) v) g ∈ UPts σ J (v.adicCompletion F) := by
  have hg' : cT (sigR σ 𝔸ᶠ[F]) (g : Matrix n n (E ⊗[F] 𝔸ᶠ[F])) * J.map (inclE (F := F) 𝔸ᶠ[F]) *
      (g : Matrix n n (E ⊗[F] 𝔸ᶠ[F])) = J.map (inclE (F := F) 𝔸ᶠ[F]) := hg
  show cT (sigR σ (v.adicCompletion F)) ((g : Matrix n n (E ⊗[F] 𝔸ᶠ[F])).map (prV (E := E) v)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * (g : Matrix n n (E ⊗[F] 𝔸ᶠ[F])).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F))
  have hJ : (J.map (inclE (F := F) 𝔸ᶠ[F])).map (prV (E := E) v) = J.map (inclE (F := F) (v.adicCompletion F)) :=
    rfl
  have hc : (cT (sigR σ 𝔸ᶠ[F]) (g : Matrix n n (E ⊗[F] 𝔸ᶠ[F]))).map (prV (E := E) v) =
      cT (sigR σ (v.adicCompletion F)) ((g : Matrix n n (E ⊗[F] 𝔸ᶠ[F])).map (prV (E := E) v)) := by
    ext i j
    exact prV_sig_lemma_8 σ v _
  rw [← hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem afsplit_coe_bc_prV (g : GL n (E ⊗[F] 𝔸ᶠ[F])) (w : HeightOneSpectrum (𝓞 F)) :
    ((bc (prV (E := E) w) g : GL n (E ⊗[F] w.adicCompletion F)) : Matrix n n (E ⊗[F] w.adicCompletion F)) =
      (g : Matrix n n (E ⊗[F] 𝔸ᶠ[F])).map (prV (E := E) w) := rfl

theorem afsplit_ker_mem (g : GL n (E ⊗[F] 𝔸ᶠ[F])) (hg : g ∈ UPts σ J 𝔸ᶠ[F]) :
    afsplitU v 1 g ∈ afsplitKer σ J v :=
  Subgroup.mem_inf.mpr ⟨afsplitU_mem v σ J 1 g (Subgroup.one_mem _) hg,
    MonoidHom.mem_ker.mpr (Units.ext ((afsplit_coe_bc_prV _ v).trans (afsplitC_prV v _ _)))⟩

theorem afsplit_ker_map (k : GL n (E ⊗[F] 𝔸ᶠ[F])) (hk : k ∈ afsplitKer σ J v) :
    (k : Matrix n n (E ⊗[F] 𝔸ᶠ[F])).map (prV (E := E) v) = 1 := by
  rw [← afsplit_coe_bc_prV, MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hk).2, Units.val_one]

private lemma afsplitC_afsplitC (M M' : Matrix n n (E ⊗[F] v.adicCompletion F))
    (N : Matrix n n (E ⊗[F] 𝔸ᶠ[F])) :
    afsplitC v M (afsplitC v M' N) = afsplitC v M N := by
  ext i j
  simp only [afsplitC_apply]
  linear_combination afsplit_om_eps_IE v (M' i j) + N i j * afsplit_eps_idem (E := E) v

theorem afsplit_left (g : GL n (E ⊗[F] 𝔸ᶠ[F])) :
    afsplitU v (bc (prV (E := E) v) g) (afsplitU v 1 g) = g :=
  Units.ext ((afsplitC_afsplitC v _ _ _).trans (afsplitC_decomp v _))

theorem afsplit_right1 (h : GL n (E ⊗[F] v.adicCompletion F)) (k : GL n (E ⊗[F] 𝔸ᶠ[F])) :
    bc (prV (E := E) v) (afsplitU v h k) = h :=
  Units.ext ((afsplit_coe_bc_prV _ v).trans (afsplitC_prV v _ _))

theorem afsplit_right2 (h : GL n (E ⊗[F] v.adicCompletion F)) (k : GL n (E ⊗[F] 𝔸ᶠ[F]))
    (hk : k ∈ afsplitKer σ J v) : afsplitU v 1 (afsplitU v h k) = k := by
  apply Units.ext
  rw [afsplitU_coe, afsplitU_coe, Units.val_one, afsplitC_afsplitC, ← afsplit_ker_map σ J v k hk,
    afsplitC_decomp]

def afsplitE : UPts σ J 𝔸ᶠ[F] ≃* (UPts σ J (v.adicCompletion F) × afsplitKer σ J v) where
  toFun g := (⟨bc (prV (E := E) v) g, afsplit_bc_mem σ J v g g.2⟩,
    ⟨afsplitU v 1 g, afsplit_ker_mem σ J v g g.2⟩)
  invFun p := ⟨afsplitU v p.1 p.2, afsplitU_mem v σ J _ _ p.1.2 (Subgroup.mem_inf.mp p.2.2).1⟩
  left_inv g := Subtype.ext (afsplit_left v (g : GL n (E ⊗[F] 𝔸ᶠ[F])))
  right_inv p := Prod.ext (Subtype.ext (afsplit_right1 v _ _))
    (Subtype.ext (afsplit_right2 σ J v _ _ p.2.2))
  map_mul' g g' := by
    refine Prod.ext (Subtype.ext (map_mul _ _ _)) (Subtype.ext ?_)
    change afsplitU v 1 ((g : GL n (E ⊗[F] 𝔸ᶠ[F])) * (g' : GL n (E ⊗[F] 𝔸ᶠ[F]))) =
      afsplitU v 1 (g : GL n (E ⊗[F] 𝔸ᶠ[F])) * afsplitU v 1 (g' : GL n (E ⊗[F] 𝔸ᶠ[F]))
    rw [← afsplitU_mul, one_mul]

theorem afsplitE_snd (g : UPts σ J 𝔸ᶠ[F]) :
    (((afsplitE σ J v g).2 : afsplitKer σ J v) : GL n _) = afsplitU v 1 (g : GL n (E ⊗[F] 𝔸ᶠ[F])) := rfl

theorem afsplitE_snd_eq_one (g : UPts σ J 𝔸ᶠ[F]) :
    (afsplitE σ J v g).2 = 1 ↔ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      bc (prV (E := E) w) (g : GL n (E ⊗[F] 𝔸ᶠ[F])) = 1 := by
  rw [← OneMemClass.coe_eq_one, afsplitE_snd]
  have h1 : ∀ w, (1 : Matrix n n (E ⊗[F] 𝔸ᶠ[F])).map (prV (E := E) w) = 1 :=
    fun w => Matrix.map_one _ (map_zero _) (map_one _)
  constructor
  · intro h w hw
    have h' : afsplitC v 1 ((g : GL n (E ⊗[F] 𝔸ᶠ[F])) : Matrix n n (E ⊗[F] 𝔸ᶠ[F])) = 1 :=
      congrArg Units.val h
    exact Units.ext (by rw [afsplit_coe_bc_prV, ← afsplitC_prV_ne v w hw 1, h', h1, Units.val_one])
  · intro h
    have key : ∀ w, (afsplitC v 1 ((g : GL n (E ⊗[F] 𝔸ᶠ[F])) : Matrix n n (E ⊗[F] 𝔸ᶠ[F]))).map
        (prV (E := E) w) = (1 : Matrix n n (E ⊗[F] 𝔸ᶠ[F])).map (prV (E := E) w) := by
      intro w
      rw [h1]
      by_cases hw : w = v
      · rw [hw, afsplitC_prV]
      · rw [afsplitC_prV_ne v w hw, ← afsplit_coe_bc_prV, h w hw, Units.val_one]
    refine Units.ext (Matrix.ext fun i j => sub_eq_zero.mp (afsplit_inj _ fun w => ?_))
    rw [map_sub, sub_eq_zero]
    exact congr_fun (congr_fun (key w) i) j

end Iso

end Formalism.UG.P
