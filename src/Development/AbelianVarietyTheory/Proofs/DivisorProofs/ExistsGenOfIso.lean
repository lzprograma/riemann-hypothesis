module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Mum.Two

section Part

variable {X X₁ X₂ Y Z : Scheme.{0}}

structure IsPart (N : LB X) (M : LB X₁) (e : X₁ ⟶ X) (π : N.ι → M.ι) : Prop where
  mem : ∀ i x, e x ∈ N.U i ↔ x ∈ M.U (π i)
  g : ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁) (z : Z) (i j : N.ι), ψ z ∈ M.U (π i) → ψ z ∈ M.U (π j) →
    gm (ψ ≫ e) z (N.U i ⊓ N.U j) (N.g i j) = gm ψ z (M.U (π i) ⊓ M.U (π j)) (M.g (π i) (π j))

def rs {N : LB X} {M : LB X₁} (e : X₁ ⟶ X) (π : N.ι → M.ι) (J : (Z ⟶ X) → N.ι) : (Z ⟶ X₁) → M.ι :=
  fun ψ => π (J (ψ ≫ e))

theorem IsPart.trans {N : LB X} {M : LB X₁} {M' : LB X₂} {e : X₁ ⟶ X} {π : N.ι → M.ι} {e' : X₂ ⟶ X₁} {π' : M.ι → M'.ι}
    (h : IsPart N M e π) (h' : IsPart M M' e' π') : IsPart N M' (e' ≫ e) (π' ∘ π) :=
  ⟨fun i x => (h.mem i (e' x)).trans (h'.mem _ x), fun Z ψ z i j hi hj => by
    rw [← Category.assoc]
    exact (h.g Z (ψ ≫ e') z i j ((h'.mem _ _).2 hi) ((h'.mem _ _).2 hj)).trans (h'.g Z ψ z _ _ hi hj)⟩

def cGen {A' A : LB Y} (c : ChartPull A' A (𝟙 Y)) (t : LB.Gen A) : LB.Gen A' :=
  ⟨fun i => res (c.le i) (t.s (c.idx i))⟩

theorem cGen_isGen {A' A : LB Y} (c : ChartPull A' A (𝟙 Y)) {t : LB.Gen A} (ht : t.IsGen) : (cGen c t).IsGen := fun i j =>
  unit_ext fun y hy => by
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U (c.idx i) ⊓ A.U (c.idx j) := ⟨c.le i hy.1, c.le j hy.2⟩
    have e := congrArg (gm (𝟙 Y) y (A.U (c.idx i) ⊓ A.U (c.idx j))) (ht (c.idx i) (c.idx j))
    rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, ← c.g y i j hy.1 hy.2] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

def cSec {A' A : LB Y} (c : ChartPull A' A (𝟙 Y)) (s : LB.Sec A) : LB.Sec A' where
  f i := (Y.presheaf.map (homOfLE (c.le i : A'.U i ≤ A.U (c.idx i))).op).hom (s.f (c.idx i))
  compat i j := fn_ext fun y hy => by
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U (c.idx i) ⊓ A.U (c.idx j) := ⟨c.le i hy.1, c.le j hy.2⟩
    have e := congrArg (gs (𝟙 Y) y (A.U (c.idx i) ⊓ A.U (c.idx j))) (s.compat (c.idx i) (c.idx j))
    rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm, ← c.g y i j hy.1 hy.2] at e
    rw [gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy]
    exact (gs_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gs_res _ y _ hy.2 _).symm))

variable {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π)
  {K : Type} [Fintype K] {φ : K → (Y ⟶ X₁)} {ε : K → ℤ}
include h

theorem IsPart.good {z : Z} {J : (Z ⟶ X) → N.ι} (hJ : Good N z J) : Good M z (rs e π J) :=
  fun ψ => (h.mem _ _).1 (hJ (ψ ≫ e))

def IsPart.up (φ : K → (Y ⟶ X₁)) (ε : K → ℤ) :
    ChartPull (LB.LinComb N (fun k => φ k ≫ e) ε) (LB.LinComb M φ ε) (𝟙 Y) :=
  have le : ∀ j : K → N.ι, LB.wchart N (fun k => φ k ≫ e) j ≤ LB.wchart M φ (fun k => π (j k)) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => (h.mem _ _).1 (Set.mem_iInter.1 hy k)
  { idx := fun j k => π (j k), le
    g := fun y j j' hj hj' => (gm_linComb N _ ε (𝟙 Y) y j j' hj hj').trans
      ((Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (by
        rw [← Category.assoc]
        exact h.g _ _ y _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k))).trans
        (gm_linComb M φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm) }

def IsPart.down (σ : M.ι → N.ι) (hσ : ∀ i, π (σ i) = i) (φ : K → (Y ⟶ X₁)) (ε : K → ℤ) :
    ChartPull (LB.LinComb M φ ε) (LB.LinComb N (fun k => φ k ≫ e) ε) (𝟙 Y) :=
  have le : ∀ j : K → M.ι, LB.wchart M φ j ≤ LB.wchart N (fun k => φ k ≫ e) (fun k => σ (j k)) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => (h.mem _ _).2 (by rw [hσ]; exact Set.mem_iInter.1 hy k)
  { idx := fun j k => σ (j k), le
    g := fun y j j' hj hj' => (gm_linComb M φ ε (𝟙 Y) y j j' hj hj').trans
      ((Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (by
        rw [← Category.assoc, h.g _ _ y _ _ (by rw [hσ]; exact Set.mem_iInter.1 hj k)
          (by rw [hσ]; exact Set.mem_iInter.1 hj' k)]
        have : ∀ a b a' b', a = a' → b = b' → gm (𝟙 Y ≫ φ k) y (M.U a ⊓ M.U b) (M.g a b) =
            gm (𝟙 Y ≫ φ k) y (M.U a' ⊓ M.U b') (M.g a' b') := by rintro _ _ _ _ rfl rfl; rfl
        exact this _ _ _ _ (hσ _).symm (hσ _).symm)).trans (gm_linComb N _ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm) }

def IsPart.gen (t : LB.Gen (LB.LinComb M φ ε)) : LB.Gen (LB.LinComb N (fun k => φ k ≫ e) ε) := cGen (h.up φ ε) t

theorem IsPart.gen_isGen {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen) : (h.gen t).IsGen := cGen_isGen _ ht

theorem IsPart.val_gen (t : LB.Gen (LB.LinComb M φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → N.ι} (hJ : Good N z J) :
    val (h.gen t) r z J = val t r z (rs e π J) :=
  (gm_res r z _ (hJ.mem (fun k => φ k ≫ e) r) _).trans
    (val_of t r z _ _ (fun k => by rw [rs, Category.assoc]; rfl)).symm

def IsPart.sec (s : LB.Sec (LB.LinComb M φ ε)) : LB.Sec (LB.LinComb N (fun k => φ k ≫ e) ε) := cSec (h.up φ ε) s

theorem IsPart.sval_sec (s : LB.Sec (LB.LinComb M φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → N.ι} (hJ : Good N z J) :
    sval (h.sec s) r z J = sval s r z (rs e π J) :=
  (gs_res r z _ (hJ.mem (fun k => φ k ≫ e) r) _).trans
    (sval_of s r z _ _ (fun k => by rw [rs, Category.assoc]; rfl)).symm

theorem IsPart.trF_eq_one (hM : M.IsLB) (r : Z ⟶ Y) (z : Z) {j j' : K → N.ι} (e₀ : ∀ k, π (j k) = π (j' k))
    (hj : ∀ k, φ k (r z) ∈ M.U (π (j k))) : trF (fun k => φ k ≫ e) ε r z j j' = 1 :=
  Finset.prod_eq_one fun k _ => by
    rw [← Category.assoc, h.g _ _ z _ _ (hj k) (e₀ k ▸ hj k)]
    have : ∀ b, π (j k) = b → gm (r ≫ φ k) z (M.U (π (j k)) ⊓ M.U b) (M.g (π (j k)) b) = 1 := by
      rintro _ rfl; exact gm_self hM _ z (hj k)
    rw [this _ (e₀ k), one_zpow]

private theorem trF_down_eq_one (hM : M.IsLB) (σ : M.ι → N.ι) (hσ : ∀ i, π (σ i) = i)
    (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → N.ι} (hJ : Good N z J) :
    trF (fun k => φ k ≫ e) ε r z (fun k => σ (rs e π J (r ≫ φ k))) (fun k => J (r ≫ φ k ≫ e)) = 1 :=
  h.trF_eq_one hM r z (fun k => (hσ _).trans (by rw [rs, Category.assoc]))
    fun k => by rw [hσ]; exact Set.mem_iInter.1 ((h.good hJ).mem φ r) k

theorem IsPart.exists_sec (hM : M.IsLB) (hπ : Function.Surjective π) (s : LB.Sec (LB.LinComb N (fun k => φ k ≫ e) ε)) :
    ∃ s' : LB.Sec (LB.LinComb M φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good N z J →
      sval s' r z (rs e π J) = sval s r z J := by
  choose σ hσ using hπ
  refine ⟨cSec (h.down σ hσ φ ε) s, fun Z r z J hJ => ?_⟩
  have m := (h.good hJ).mem φ r
  refine (gs_res r z _ m _).trans ((sec_trans s r z ((h.down σ hσ φ ε).le _ m) (hJ.mem _ r)).trans ?_)
  dsimp only [IsPart.down]
  rw [trF_down_eq_one h hM σ hσ r z hJ, Units.val_one, _root_.one_mul]; rfl

theorem IsPart.exists_gen (hM : M.IsLB) (hπ : Function.Surjective π) (t : LB.Gen (LB.LinComb N (fun k => φ k ≫ e) ε))
    (ht : t.IsGen) : ∃ t' : LB.Gen (LB.LinComb M φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good N z J →
      val t' r z (rs e π J) = val t r z J := by
  choose σ hσ using hπ
  refine ⟨cGen (h.down σ hσ φ ε) t, cGen_isGen _ ht, fun Z r z J hJ => ?_⟩
  have m := (h.good hJ).mem φ r
  refine (gm_res r z _ m _).trans ((gen_trans ht r z ((h.down σ hσ φ ε).le _ m) (hJ.mem _ r)).trans ?_)
  dsimp only [IsPart.down]
  rw [trF_down_eq_one h hM σ hσ r z hJ, _root_.one_mul]; rfl

end Part

section Iso

variable {X X₁ X₂ Y Y₀ Z : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} {M' : LB X₂} {e' : X₂ ⟶ X}
  {π' : N.ι → M'.ι} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y₀ ⟶ X₁)} {ε : K → ℤ} {β : Y ⟶ Y₀}
  {φ' : K' → (Y ⟶ X₂)} {ε' : K' → ℤ}

def isoVal (w : LB.Iso (LB.LinComb M' φ' ε') ((LB.LinComb M φ ε).pull β)) (p : Z ⟶ Y) (z : Z) (J : (Z ⟶ X₁) → M.ι)
    (J' : (Z ⟶ X₂) → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun _ k => J (p ≫ β ≫ φ k), fun k => J' (p ≫ φ' k)))

theorem gm_div_pull (p : Z ⟶ Y) (z : Z) (a b : (PUnit.{1} → K → M.ι) × (K' → M'.ι))
    (ha : p z ∈ (LB.div ((LB.LinComb M φ ε).pull β) (LB.LinComb M' φ' ε')).U a)
    (hb : p z ∈ (LB.div ((LB.LinComb M φ ε).pull β) (LB.LinComb M' φ' ε')).U b) :
    gm p z _ ((LB.div ((LB.LinComb M φ ε).pull β) (LB.LinComb M' φ' ε')).g a b) =
      trF φ ε (p ≫ β) z (a.1 PUnit.unit) (b.1 PUnit.unit) * (trF φ' ε' p z a.2 b.2)⁻¹ :=
  (gm_div (LB.LinComb M' φ' ε') ((LB.LinComb M φ ε).pull β) p z a b ⟨ha, hb⟩).trans (congrArg₂ (· * ·)
    ((gm_pull_g (LB.LinComb M φ ε) β p z a.1 b.1 ha.1 hb.1).trans
      (gm_linComb M φ ε (p ≫ β) z _ _ (mem_pull.1 ha.1) (mem_pull.1 hb.1)))
    (congrArg (·⁻¹) (gm_linComb M' φ' ε' p z _ _ ha.2 hb.2)))

variable (h : IsPart N M e π) (h' : IsPart N M' e' π')
include h h'

theorem trF_two (p : Z ⟶ Y) (z : Z) (j j' : K ⊕ K' → N.ι)
    (hj : p z ∈ LB.wchart N (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) j)
    (hj' : p z ∈ LB.wchart N (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) j') :
    trF (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) (Sum.elim ε (fun k => - ε' k)) p z j j' =
      trF φ ε (p ≫ β) z (fun k => π (j (.inl k))) (fun k => π (j' (.inl k))) *
        (trF φ' ε' p z (fun k => π' (j (.inr k))) (fun k => π' (j' (.inr k))))⁻¹ := by
  rw [trF, trF, trF, Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
    (Finset.prod_congr rfl fun k _ => (zpow_neg _ _).trans (congrArg (fun u => (u ^ ε' k)⁻¹) ?_))
  · simp only [Sum.elim_inl, ← Category.assoc]
    exact h.g _ ((p ≫ β) ≫ φ k) z _ _ ((h.mem _ _).1 (Set.mem_iInter.1 hj (.inl k)))
      ((h.mem _ _).1 (Set.mem_iInter.1 hj' (.inl k)))
  · simp only [Sum.elim_inr, ← Category.assoc]
    exact h'.g _ (p ≫ φ' k) z _ _ ((h'.mem _ _).1 (Set.mem_iInter.1 hj (.inr k)))
      ((h'.mem _ _).1 (Set.mem_iInter.1 hj' (.inr k)))

theorem exists_gen_of_iso (w : LB.Iso (LB.LinComb M' φ' ε') ((LB.LinComb M φ ε).pull β)) (hw : w.IsGen) :
    ∃ t : LB.Gen (LB.LinComb N (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) (Sum.elim ε (fun k => - ε' k))),
      t.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ Y) (z : Z) (J), Good N z J →
        val t p z J = isoVal w p z (rs e π J) (rs e' π' J) := by
  have le : ∀ j : K ⊕ K' → N.ι, LB.wchart N (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) j ≤
      (LB.div ((LB.LinComb M φ ε).pull β) (LB.LinComb M' φ' ε')).U
        (fun _ k => π (j (.inl k)), fun k => π' (j (.inr k))) := fun j y hy =>
    ⟨mem_pull.2 (Set.mem_iInter.2 fun k => (h.mem _ _).1 (Set.mem_iInter.1 hy (.inl k))),
      Set.mem_iInter.2 fun k => (h'.mem _ _).1 (Set.mem_iInter.1 hy (.inr k))⟩
  let c : ChartPull (LB.LinComb N (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) (Sum.elim ε (fun k => - ε' k)))
      (LB.div ((LB.LinComb M φ ε).pull β) (LB.LinComb M' φ' ε')) (𝟙 Y) :=
    { idx := fun j => (fun _ k => π (j (.inl k)), fun k => π' (j (.inr k))), le
      g := fun y j j' hj hj' => (gm_linComb N _ _ (𝟙 Y) y j j' hj hj').trans ((trF_two h h' (𝟙 Y) y j j' hj hj').trans
        (gm_div_pull (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm) }
  refine ⟨cGen c w, cGen_isGen c hw, fun Z p z J hJ => (gm_res p z _ (hJ.mem _ p) _).trans ?_⟩
  simp only [isoVal, rs, c]
  rfl

theorem exists_iso_of_gen (hM : M.IsLB) (hM' : M'.IsLB) (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
    (t : LB.Gen (LB.LinComb N (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) (Sum.elim ε (fun k => - ε' k))))
    (ht : t.IsGen) : ∃ w : LB.Iso (LB.LinComb M' φ' ε') ((LB.LinComb M φ ε).pull β), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (p : Z ⟶ Y) (z : Z) (J), Good N z J →
        isoVal w p z (rs e π J) (rs e' π' J) = val t p z J := by
  choose σ hσ using hπ
  choose σ' hσ' using hπ'
  let ix : (PUnit.{1} → K → M.ι) × (K' → M'.ι) → K ⊕ K' → N.ι := fun a =>
    Sum.elim (fun k => σ (a.1 PUnit.unit k)) (fun k => σ' (a.2 k))
  have le : ∀ a, (LB.div ((LB.LinComb M φ ε).pull β) (LB.LinComb M' φ' ε')).U a ≤
      LB.wchart N (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) (ix a) := fun a y hy =>
    Set.mem_iInter.2 fun k => by
      rcases k with k | k
      · exact (h.mem _ _).2 ((hσ _).symm ▸ Set.mem_iInter.1 (mem_pull.1 hy.1) k)
      · exact (h'.mem _ _).2 ((hσ' _).symm ▸ Set.mem_iInter.1 hy.2 k)
  have i₁ : ∀ a, (fun k => π (ix a (.inl k))) = a.1 PUnit.unit := fun a => funext fun k => hσ _
  have i₂ : ∀ a, (fun k => π' (ix a (.inr k))) = a.2 := fun a => funext fun k => hσ' _
  let c : ChartPull (LB.div ((LB.LinComb M φ ε).pull β) (LB.LinComb M' φ' ε'))
      (LB.LinComb N (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) (Sum.elim ε (fun k => - ε' k))) (𝟙 Y) :=
    { idx := ix, le
      g := fun y a b ha hb => (gm_div_pull (𝟙 Y) y _ _ ha hb).trans (Eq.symm
        ((gm_linComb N _ _ (𝟙 Y) y _ _ (le a ha) (le b hb)).trans ((trF_two h h' (𝟙 Y) y _ _ (le a ha) (le b hb)).trans
          (congrArg₂ (· * ·) (congrArg₂ (trF φ ε (𝟙 Y ≫ β) y) (i₁ a) (i₁ b))
            (congrArg (·⁻¹) (congrArg₂ (trF φ' ε' (𝟙 Y) y) (i₂ a) (i₂ b))))))) }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z p z J hJ => ?_⟩
  have m₁ : (p ≫ β) z ∈ LB.wchart M φ (fun k => rs e π J (p ≫ β ≫ φ k)) :=
    Set.mem_iInter.2 fun k => h.good hJ (p ≫ β ≫ φ k)
  have m₂ := (h'.good hJ).mem φ' p
  have m : p z ∈ (LB.div ((LB.LinComb M φ ε).pull β) (LB.LinComb M' φ' ε')).U
      (fun _ k => rs e π J (p ≫ β ≫ φ k), fun k => rs e' π' J (p ≫ φ' k)) := ⟨mem_pull.2 m₁, m₂⟩
  have n := hJ.mem (Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e')) p
  refine (gm_res p z _ m _).trans ((gen_trans ht p z (le _ m) n).trans ?_)
  have a₁ : (fun k => π (J (p ≫ Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e') (.inl k)))) =
      fun k => rs e π J (p ≫ β ≫ φ k) := funext fun k => by simp only [rs, Sum.elim_inl, Category.assoc]
  have a₂ : (fun k => π' (J (p ≫ Sum.elim (fun k => β ≫ φ k ≫ e) (fun k => φ' k ≫ e') (.inr k)))) =
      fun k => rs e' π' J (p ≫ φ' k) := funext fun k => by simp only [rs, Sum.elim_inr, Category.assoc]
  have b₁ := (congrArg₂ (trF φ ε (p ≫ β) z) (i₁ (fun _ k => rs e π J (p ≫ β ≫ φ k), fun k => rs e' π' J (p ≫ φ' k))) a₁).trans
    (mul_eq_left.1 (trF_trans hM φ ε (p ≫ β) z m₁ m₁ m₁))
  have b₂ := (congrArg₂ (trF φ' ε' p z) (i₂ (fun _ k => rs e π J (p ≫ β ≫ φ k), fun k => rs e' π' J (p ≫ φ' k))) a₂).trans
    (mul_eq_left.1 (trF_trans hM' φ' ε' p z m₂ m₂ m₂))
  exact (congrArg (· * val t p z J) ((trF_two h h' p z _ _ (le _ m) n).trans
    ((congrArg₂ (fun u v => u * v⁻¹) b₁ b₂).trans (mul_inv_cancel 1)))).trans (_root_.one_mul _)

end Iso

section Join

variable {X₁ X₂ Z : Scheme.{0}}

theorem inl_ne_inr (x : X₁) (y : X₂) : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ≠ (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) y := fun h =>
  (isCompl_range_inl_inr X₁ X₂).1 (Set.singleton_subset_iff.2 ⟨x, rfl⟩) (Set.singleton_subset_iff.2 ⟨y, h.symm⟩) rfl

theorem inl_or_inr (p : (X₁ ⨿ X₂ : Scheme.{0})) :
    (∃ x, (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x = p) ∨ ∃ y, (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) y = p :=
  (isCompl_range_inl_inr X₁ X₂).sup_eq_top.ge (Set.mem_univ p)

def jU (U₁ : X₁.Opens) (U₂ : X₂.Opens) : (X₁ ⨿ X₂).Opens :=
  (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ''ᵁ U₁ ⊔ (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ''ᵁ U₂

theorem mem_jU_inl (U₁ : X₁.Opens) (U₂ : X₂.Opens) (x : X₁) : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈ jU U₁ U₂ ↔ x ∈ U₁ :=
  ⟨fun | Or.inl ⟨_, hy, e⟩ => (coprod.inl : X₁ ⟶ X₁ ⨿ X₂).isOpenEmbedding.injective e ▸ hy
       | Or.inr ⟨_, _, e⟩ => (inl_ne_inr x _ e.symm).elim,
   fun h => Or.inl ⟨x, h, rfl⟩⟩

theorem mem_jU_inr (U₁ : X₁.Opens) (U₂ : X₂.Opens) (x : X₂) : (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈ jU U₁ U₂ ↔ x ∈ U₂ :=
  ⟨fun | Or.inl ⟨_, _, e⟩ => (inl_ne_inr _ x e).elim
       | Or.inr ⟨_, hy, e⟩ => (coprod.inr : X₂ ⟶ X₁ ⨿ X₂).isOpenEmbedding.injective e ▸ hy,
   fun h => Or.inr ⟨x, h, rfl⟩⟩

theorem exists_glue (W : (X₁ ⨿ X₂).Opens) (U₁ : X₁.Opens) (U₂ : X₂.Opens)
    (h₁ : ∀ x, (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈ W → x ∈ U₁) (h₂ : ∀ x, (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈ W → x ∈ U₂)
    (a₁ : Γ(X₁, U₁)ˣ) (a₂ : Γ(X₂, U₂)ˣ) : ∃ a : Γ(X₁ ⨿ X₂, W)ˣ,
      (∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁) (z : Z), (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) (ψ z) ∈ W →
        gm (ψ ≫ coprod.inl) z W a = gm ψ z U₁ a₁) ∧
      ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₂) (z : Z), (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (ψ z) ∈ W →
        gm (ψ ≫ coprod.inr) z W a = gm ψ z U₂ a₂ := by
  obtain ⟨b₁, e₁⟩ := exists_ext_unit (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ⁻¹ᵁ W) (res h₁ a₁)
  obtain ⟨b₂, e₂⟩ := exists_ext_unit (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ⁻¹ᵁ W) (res h₂ a₂)
  let V : Bool → (X₁ ⨿ X₂).Opens := Bool.rec
    ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ''ᵁ ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ⁻¹ᵁ W))
    ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ''ᵁ ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ⁻¹ᵁ W))
  have le : ∀ b, V b ≤ W := by rintro (_ | _) _ ⟨y, hy, rfl⟩ <;> exact hy
  obtain ⟨a, ha⟩ := glue_unit W V le (fun p hp => TopologicalSpace.Opens.mem_iSup.2 <|
      (inl_or_inr p).elim (fun ⟨x, hx⟩ => by subst hx; exact ⟨false, x, hp, rfl⟩)
        (fun ⟨x, hx⟩ => by subst hx; exact ⟨true, x, hp, rfl⟩))
    (Bool.rec (motive := fun b => Γ(X₁ ⨿ X₂, V b)ˣ) b₁ b₂) (by
      rintro (_ | _) (_ | _) p ⟨hp, hp'⟩ <;> try rfl
      · obtain ⟨x, -, e⟩ := hp; obtain ⟨y, -, e'⟩ := hp'; exact (inl_ne_inr x y (e.trans e'.symm)).elim
      · obtain ⟨x, -, e⟩ := hp; obtain ⟨y, -, e'⟩ := hp'; exact (inl_ne_inr y x (e'.trans e.symm)).elim)
  exact ⟨a,
    fun Z ψ z hz => (gm_res _ z (le false) ⟨ψ z, hz, rfl⟩ a).symm.trans ((congrArg _ (ha false)).trans ((e₁ Z ψ z hz).trans (gm_res ψ z _ hz _))),
    fun Z ψ z hz => (gm_res _ z (le true) ⟨ψ z, hz, rfl⟩ a).symm.trans ((congrArg _ (ha true)).trans ((e₂ Z ψ z hz).trans (gm_res ψ z _ hz _)))⟩

theorem unit_ext_coprod {W : (X₁ ⨿ X₂).Opens} {a b : Γ(X₁ ⨿ X₂, W)ˣ}
    (h₁ : ∀ x, (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈ W → gm coprod.inl x W a = gm coprod.inl x W b)
    (h₂ : ∀ x, (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈ W → gm coprod.inr x W a = gm coprod.inr x W b) : a = b :=
  unit_ext fun p hp => (inl_or_inr p).elim (fun ⟨x, e⟩ => e ▸ gm_inj _ x (e ▸ hp) (e ▸ hp) (h₁ x (e ▸ hp)))
    (fun ⟨x, e⟩ => e ▸ gm_inj _ x (e ▸ hp) (e ▸ hp) (h₂ x (e ▸ hp)))

variable (M₁ : LB X₁) (M₂ : LB X₂)

theorem exists_join_g (p q : M₁.ι × M₂.ι) :
    ∃ a : Γ(X₁ ⨿ X₂, jU (M₁.U p.1) (M₂.U p.2) ⊓ jU (M₁.U q.1) (M₂.U q.2))ˣ,
      (∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁) (z : Z), ψ z ∈ M₁.U p.1 → ψ z ∈ M₁.U q.1 →
        gm (ψ ≫ coprod.inl) z _ a = gm ψ z _ (M₁.g p.1 q.1)) ∧
      ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₂) (z : Z), ψ z ∈ M₂.U p.2 → ψ z ∈ M₂.U q.2 →
        gm (ψ ≫ coprod.inr) z _ a = gm ψ z _ (M₂.g p.2 q.2) := by
  obtain ⟨a, h₁, h₂⟩ := exists_glue (jU (M₁.U p.1) (M₂.U p.2) ⊓ jU (M₁.U q.1) (M₂.U q.2))
    (M₁.U p.1 ⊓ M₁.U q.1) (M₂.U p.2 ⊓ M₂.U q.2)
    (fun x hx => ⟨(mem_jU_inl _ _ x).1 hx.1, (mem_jU_inl _ _ x).1 hx.2⟩)
    (fun x hx => ⟨(mem_jU_inr _ _ x).1 hx.1, (mem_jU_inr _ _ x).1 hx.2⟩) (M₁.g p.1 q.1) (M₂.g p.2 q.2)
  exact ⟨a, fun Z ψ z a b => h₁ Z ψ z ⟨(mem_jU_inl _ _ _).2 a, (mem_jU_inl _ _ _).2 b⟩,
    fun Z ψ z a b => h₂ Z ψ z ⟨(mem_jU_inr _ _ _).2 a, (mem_jU_inr _ _ _).2 b⟩⟩

def join : LB (X₁ ⨿ X₂) :=
  ⟨M₁.ι × M₂.ι, fun p => jU (M₁.U p.1) (M₂.U p.2), fun p q => (exists_join_g M₁ M₂ p q).choose⟩

theorem isPart_inl : IsPart (join M₁ M₂) M₁ coprod.inl Prod.fst :=
  ⟨fun _ x => mem_jU_inl _ _ x, fun Z ψ z p q => (exists_join_g M₁ M₂ p q).choose_spec.1 Z ψ z⟩

theorem isPart_inr : IsPart (join M₁ M₂) M₂ coprod.inr Prod.snd :=
  ⟨fun _ x => mem_jU_inr _ _ x, fun Z ψ z p q => (exists_join_g M₁ M₂ p q).choose_spec.2 Z ψ z⟩

variable {M₁ M₂}

abbrev rl (J : (Z ⟶ X₁ ⨿ X₂) → (join M₁ M₂).ι) : (Z ⟶ X₁) → M₁.ι := rs (N := join M₁ M₂) coprod.inl Prod.fst J

abbrev rr (J : (Z ⟶ X₁ ⨿ X₂) → (join M₁ M₂).ι) : (Z ⟶ X₂) → M₂.ι := rs (N := join M₁ M₂) coprod.inr Prod.snd J

theorem nonempty_idx {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) [h : Nonempty X] : Nonempty M.ι :=
  h.elim fun x => (exists_chart hM x).nonempty

theorem fst_surjective (h₂ : M₂.IsLB) [Nonempty X₂] : Function.Surjective (Prod.fst : (join M₁ M₂).ι → M₁.ι) :=
  fun i => (nonempty_idx h₂).elim fun j => ⟨(i, j), rfl⟩

theorem snd_surjective (h₁ : M₁.IsLB) [Nonempty X₁] : Function.Surjective (Prod.snd : (join M₁ M₂).ι → M₂.ι) :=
  fun j => (nonempty_idx h₁).elim fun i => ⟨(i, j), rfl⟩

private theorem join_unit_compat {X X' : Scheme.{0}} {N : LB X} {M : LB X'} (hM : M.IsLB) {f : X' ⟶ X} {π : N.ι → M.ι}
    (p : IsPart N M f π) {i : N.ι} {x : X'} (hsub : N.U i ≤ N.U i ⊓ N.U i) (hx : f x ∈ N.U i) :
    gm f x (N.U i) (res hsub (N.g i i)) = gm f x (N.U i) 1 := by
  have m := (p.mem _ _).1 hx
  have g := p.g _ (𝟙 X') x i i m m
  rw [Category.id_comp] at g
  exact (gm_res _ x _ hx _).trans (g.trans ((gm_self hM (𝟙 _) x m).trans (map_one _).symm))

private theorem join_cocycle_compat {X X' : Scheme.{0}} {N : LB X} {M : LB X'} (hM : M.IsLB) {f : X' ⟶ X} {π : N.ι → M.ι}
    (p : IsPart N M f π) {i j k : N.ι} {x : X'}
    (h₁ : (N.U i ⊓ N.U j) ⊓ N.U k ≤ N.U i ⊓ N.U j)
    (h₂ : (N.U i ⊓ N.U j) ⊓ N.U k ≤ N.U j ⊓ N.U k)
    (h₃ : (N.U i ⊓ N.U j) ⊓ N.U k ≤ N.U i ⊓ N.U k)
    (hx : f x ∈ (N.U i ⊓ N.U j) ⊓ N.U k) :
    gm f x ((N.U i ⊓ N.U j) ⊓ N.U k) (res h₁ (N.g i j) * res h₂ (N.g j k)) =
      gm f x ((N.U i ⊓ N.U j) ⊓ N.U k) (res h₃ (N.g i k)) := by
  have a := (p.mem _ _).1 hx.1.1; have b := (p.mem _ _).1 hx.1.2; have c := (p.mem _ _).1 hx.2
  have g := fun i' j' hi' hj' => by simpa only [Category.id_comp] using p.g _ (𝟙 X') x i' j' hi' hj'
  exact (map_mul _ _ _).trans ((congrArg₂ (· * ·) ((gm_res _ x _ hx _).trans (g i j a b))
    ((gm_res _ x _ hx _).trans (g j k b c))).trans ((gm_cocycle hM (𝟙 _) x a b c).trans
      ((gm_res _ x _ hx _).trans (g i k a c)).symm))

theorem join_isLB (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) [Nonempty X₁] [Nonempty X₂] : (join M₁ M₂).IsLB := by
  refine ⟨top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ?_,
    fun i => unit_ext_coprod (fun _ hx => join_unit_compat h₁ (isPart_inl M₁ M₂) _ hx)
      (fun _ hx => join_unit_compat h₂ (isPart_inr M₁ M₂) _ hx),
    fun i j k => unit_ext_coprod (fun _ hx => join_cocycle_compat h₁ (isPart_inl M₁ M₂) _ _ _ hx)
      (fun _ hx => join_cocycle_compat h₂ (isPart_inr M₁ M₂) _ _ _ hx)⟩
  rcases inl_or_inr p with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · obtain ⟨i, hi⟩ := exists_chart h₁ x; obtain ⟨j⟩ := nonempty_idx h₂; exact ⟨(i, j), (mem_jU_inl _ _ x).2 hi⟩
  · obtain ⟨j, hj⟩ := exists_chart h₂ x; obtain ⟨i⟩ := nonempty_idx h₁; exact ⟨(i, j), (mem_jU_inr _ _ x).2 hj⟩

theorem exists_good_join (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) [Nonempty X₁] [Nonempty X₂] {z : Z} {J₁ : (Z ⟶ X₁) → M₁.ι}
    {J₂ : (Z ⟶ X₂) → M₂.ι} (g₁ : Good M₁ z J₁) (g₂ : Good M₂ z J₂) :
    ∃ J, Good (join M₁ M₂) z J ∧ rl J = J₁ ∧ rr J = J₂ := by
  obtain ⟨i₀⟩ := nonempty_idx h₁; obtain ⟨j₀⟩ := nonempty_idx h₂
  obtain ⟨J, hJ, e⟩ := exists_good (join M₁ M₂) (join_isLB h₁ h₂) z (K := (Z ⟶ X₁) ⊕ (Z ⟶ X₂))
    (Sum.elim (· ≫ coprod.inl) (· ≫ coprod.inr)) (Sum.elim (fun ψ => (J₁ ψ, j₀)) (fun ψ => (i₀, J₂ ψ))) (by
      rintro (a | a) (b | b) e
      · rw [(cancel_mono (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)).1 e]
      · exact (inl_ne_inr (a z) (b z) (congrArg (fun q : Z ⟶ X₁ ⨿ X₂ => q z) e)).elim
      · exact (inl_ne_inr (b z) (a z) (congrArg (fun q : Z ⟶ X₁ ⨿ X₂ => q z) e).symm).elim
      · rw [(cancel_mono (coprod.inr : X₂ ⟶ X₁ ⨿ X₂)).1 e])
    (by rintro (a | a) <;> [exact (mem_jU_inl _ _ _).2 (g₁ a); exact (mem_jU_inr _ _ _).2 (g₂ a)])
  exact ⟨J, hJ, funext fun ψ => congrArg Prod.fst (e (.inl ψ)), funext fun ψ => congrArg Prod.snd (e (.inr ψ))⟩

end Join

end GlobalTheory.Mum.Two
