module

public import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace UpperTheory.DirectSumIndependence

private abbrev P (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    Ht q (sch.obj (Spec A)) n i →+ Ht q (sch.obj (Spec B)) n i :=
  pull _ (sch.map (Spec.map f)) (tw q i) n

private theorem pullback_comp₂ (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : Ht q (sch.obj (Spec A)) n i) : P q i n (f ≫ g) x = P q i n g (P q i n f x) := by
  show pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n x = _
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

private theorem isUnit_of_hom {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) :
    IsUnit (q : B) := by
  simpa using h.map f.hom

private theorem chase (b1 : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J]
    (D D' : J ⥤ CommRingCat.{0}) (α : D ⟶ D') (c : Cocone D) (hc : IsColimit c)
    (c' : Cocone D') (hc' : IsColimit c') (g : c.pt ⟶ c'.pt)
    (hg : ∀ j, c.ι.app j ≫ g = α.app j ≫ c'.ι.app j)
    (hα : ∀ j, RE q i (α.app j)) (hq : ∀ j, IsUnit (q : D.obj j)) : RE q i g := fun n => by
  change Function.Bijective (P q i n g)
  obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
  have hqc : IsUnit (q : c.pt) := isUnit_of_hom (c.ι.app j0) (hq j0)
  have comm (j : J) (y) : P q i n g (P q i n (c.ι.app j) y) =
      P q i n (c'.ι.app j) (P q i n (α.app j) y) := by
    rw [← pullback_comp₂, ← pullback_comp₂, hg]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun z => ?_⟩
  · obtain ⟨j, y, hy⟩ := (b1 q D c hc n i).1 x hqc
    change P q i n (c.ι.app j) y = x at hy
    subst hy
    rw [comm] at hx
    obtain ⟨k, f, hf⟩ :=
      (b1 q D' c' hc' n i).2 j (P q i n (α.app j) y) (isUnit_of_hom (α.app j) (hq j)) hx
    change P q i n (D'.map f) (P q i n (α.app j) y) = 0 at hf
    rw [← pullback_comp₂, ← α.naturality f, pullback_comp₂] at hf
    rw [← c.w f, pullback_comp₂, (hα k n).1 (hf.trans (map_zero _).symm), map_zero]
  · obtain ⟨j, y', hy'⟩ := (b1 q D' c' hc' n i).1 z (isUnit_of_hom g hqc)
    change P q i n (c'.ι.app j) y' = z at hy'
    obtain ⟨y, rfl⟩ := (hα j n).2 y'
    exact ⟨P q i n (c.ι.app j) y, (comm j y).trans hy'⟩

end UpperTheory.DirectSumIndependence

theorem UpperTheory.cohomology_continuity_filtered_colimit_rings :
    LateralTheory.E.t_E3Cut.Limit := by
  intro hyp q _ i A Y φ hq hEt C c hc Y' w φ' hp
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hc
  have : IsConnected J := IsFiltered.isConnected J
  let φJ : (Functor.const J).obj A ⟶ (Functor.const J).obj Y := (Functor.const J).map φ
  let sq := IsPushout.of_hasPushout φJ t
  let c' : Cocone (pushout φJ t) :=
    { pt := Y'
      ι := pushout.desc ((Functor.const J).map w) (s ≫ (Functor.const J).map φ')
        (NatTrans.ext <| funext fun j => by simp [φJ, hp.w, reassoc_of% (hts j).2]) }
  have hinl : pushout.inl φJ t ≫ c'.ι = (Functor.const J).map w := by simp [c']
  have hinr (j : J) : s.app j ≫ φ' = (pushout.inr φJ t).app j ≫ c'.ι.app j := by
    simpa using (NatTrans.congr_app (by simp [c'] : pushout.inr φJ t ≫ c'.ι =
      s ≫ (Functor.const J).map φ') j).symm
  have hc' : IsColimit c' := sq.isColimitOfIsColimitOfIsPushout
    (constCocone J A) (constCocone J Y) (Cocone.mk C s) c'
    (isColimitConstCocone J A) (isColimitConstCocone J Y) hs hp
    (by simp [φJ]) (by simp [hts])
    (fun j => by simpa using (NatTrans.congr_app hinl j).symm) hinr
  exact UpperTheory.DirectSumIndependence.chase hyp.2.2.2.2.2.2.1 q i D (pushout φJ t)
    (pushout.inr φJ t) (Cocone.mk C s) hs c' hc' φ' hinr
    (fun j => hEt _ _ (hts j).1 _ _ _ (sq.app j))
    (fun j => UpperTheory.DirectSumIndependence.isUnit_of_hom (t.app j) hq)
