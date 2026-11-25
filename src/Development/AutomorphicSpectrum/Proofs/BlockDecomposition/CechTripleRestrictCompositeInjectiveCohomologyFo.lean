module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullOWOverComp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocOAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPull1InjectiveOfSepGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepOfFactoringCover
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits

namespace GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R]

def secA {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (p : Pair φ) : Sec s p.1.2.1 →ₐ[R] Sec s' p.1.1.1 :=
  { secPull s s' p with commutes' := (semiHom_secPull h p).map_algebraMap }

theorem kunneth_open (A B : Over (Sp R)) (U : A.left.affineOpens) (V : B.left.affineOpens) :
    ∃ hV : IsAffineOpen ((fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1),
      Function.Bijective (Algebra.TensorProduct.lift
        (secA (wOver (fst A B)) ⟨(⟨_, hV⟩, U), inf_le_left⟩)
        (secA (wOver (snd A B)) ⟨(⟨_, hV⟩, V), inf_le_right⟩) (fun _ _ ↦ Commute.all _ _)) := by
  let Sa := Sec A.hom U.1
  let Sb := Sec B.hom V.1
  let iU := affPt A.hom U
  let iV := affPt B.hom V
  have eU : iU ≫ A.hom = spMap (algebraMap R Sa) := affPt_w _ _
  have eV : iV ≫ B.hom = spMap (algebraMap R Sb) := affPt_w _ _
  let ma : pullback (spMap (algebraMap R Sa)) (spMap (algebraMap R Sb)) ⟶ pullback A.hom B.hom :=
    pullback.map _ _ _ _ iU iV (𝟙 _) (by rw [Category.comp_id, eU]) (by rw [Category.comp_id, eV])
  have : IsOpenImmersion ma :=
    CategoryTheory.MorphismProperty.pullbackMap (P := @IsOpenImmersion) (f := spMap (algebraMap R Sa)) (g := spMap (algebraMap R Sb))
      (IsAffineOpen.isOpenImmersion_fromSpec U.2) (IsAffineOpen.isOpenImmersion_fromSpec V.2) eU.symm eV.symm
  let j : Spec (CommRingCat.of (Sa ⊗[R] Sb)) ⟶ pullback A.hom B.hom := (pullbackSpecIso R Sa Sb).inv ≫ ma
  have hj : j.opensRange = (fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1 := by
    apply TopologicalSpace.Opens.ext
    have e1 : Set.range j = Set.range ma := Set.ext fun x ↦
      ⟨fun ⟨y, hy⟩ ↦ ⟨(pullbackSpecIso R Sa Sb).inv y, hy ▸ (Scheme.Hom.comp_apply _ _ y).symm⟩,
       fun ⟨y, hy⟩ ↦ ⟨(pullbackSpecIso R Sa Sb).hom y, by simp [j, ← Scheme.Hom.comp_apply, hy]⟩⟩
    have e2 := Scheme.Pullback.range_map (spMap (algebraMap R Sa)) (spMap (algebraMap R Sb)) A.hom B.hom iU iV (𝟙 _)
      (by rw [Category.comp_id, eU]) (by rw [Category.comp_id, eV])
    simp only [Scheme.Hom.coe_opensRange, e1]
    refine e2.trans ?_
    rw [show Set.range iU = (U.1 : Set A.left) from U.2.range_fromSpec, show Set.range iV = (V.1 : Set B.left) from V.2.range_fromSpec]; rfl
  have hV : IsAffineOpen ((fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1) := hj ▸ isAffineOpen_opensRange j
  refine ⟨hV, ?_⟩
  let κ : Sa ⊗[R] Sb →ₐ[R] Sec (A ⊗ B).hom ((fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1) := Algebra.TensorProduct.lift
    (secA (wOver (fst A B)) ⟨(⟨_, hV⟩, U), inf_le_left⟩)
    (secA (wOver (snd A B)) ⟨(⟨_, hV⟩, V), inf_le_right⟩) (fun _ _ ↦ Commute.all _ _)
  have hk : spMap κ.toRingHom ≫ j = hV.fromSpec := by
    apply pullback.hom_ext
    · have l : κ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = secPull A.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, U), inf_le_left⟩ :=
        RingHom.ext fun x ↦ by change κ (x ⊗ₜ 1) = _; rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]; rfl
      have m2 : spMap κ.toRingHom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
          spMap (secPull A.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, U), inf_le_left⟩) := by rw [← l, spMap_comp]
      rw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc (pullbackSpecIso R Sa Sb).inv,
        pullbackSpecIso_inv_fst, ← Category.assoc, m2]
      exact secPull_affPt (φ := (fst A B).left) A.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, U), inf_le_left⟩
    · have l : κ.toRingHom.comp (Algebra.TensorProduct.includeRight : Sb →ₐ[R] Sa ⊗[R] Sb).toRingHom = secPull B.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, V), inf_le_right⟩ :=
        RingHom.ext fun x ↦ by change κ (1 ⊗ₜ x) = _; rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]; rfl
      have m2 : spMap κ.toRingHom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Sb →ₐ[R] Sa ⊗[R] Sb).toRingHom) =
          spMap (secPull B.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, V), inf_le_right⟩) := by rw [← l, spMap_comp]
      rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc (pullbackSpecIso R Sa Sb).inv,
        pullbackSpecIso_inv_snd, ← Category.assoc]
      exact (congrArg (· ≫ iV) m2).trans (secPull_affPt (φ := (snd A B).left) B.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, V), inf_le_right⟩)
  have : IsOpenImmersion (spMap κ.toRingHom ≫ j) := hk ▸ IsAffineOpen.isOpenImmersion_fromSpec hV
  have : IsOpenImmersion (spMap κ.toRingHom) := IsOpenImmersion.of_comp _ j
  have : Epi (spMap κ.toRingHom).base := (TopCat.epi_iff_surjective _).2 fun t ↦ by
    obtain ⟨y, hy⟩ := (hV.range_fromSpec ▸ hj ▸ Set.mem_range_self t : j t ∈ Set.range hV.fromSpec)
    exact ⟨y, j.injective (by rw [← hy, ← hk]; rfl)⟩
  have : IsIso (spMap κ.toRingHom) := IsOpenImmersion.isIso _
  have : IsIso (CommRingCat.ofHom κ.toRingHom) := by
    let g := Spec.preimage (inv (Spec.map (CommRingCat.ofHom κ.toRingHom)))
    exact ⟨g, Spec.map_injective (by simp [g]), Spec.map_injective (by simp [g])⟩
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom κ.toRingHom)

section Comp
variable {R' R'' : Type} [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem isPullO_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) {a : HO1 s} {a' : HO1 s'} {a'' : HO1 s''}
    (p : IsPullO h a a') (p' : IsPullO h' a' a'') : IsPullO h'' a a'' := by
  apply GlobalTheory.CompanionTheory.Axis.PullO.isPullO_comp <;> assumption
end Comp

section Over

theorem isPullO_over_comp {Y Z T : Over (Sp R)} (f : Y ⟶ Z) (g : Z ⟶ T) {a : HO1 T.hom} {a' : HO1 Z.hom}
    {a'' : HO1 Y.hom} (p : IsPullO (wOver g) a a') (p' : IsPullO (wOver f) a' a'') :
    IsPullO (wOver (f ≫ g)) a a'' :=
  isPullO_comp (wOver g) (wOver f) (wOver (f ≫ g)) p p'

theorem isPullO_over_id (Y : Over (Sp R)) (c : HO1 Y.hom) : IsPullO (wOver (𝟙 Y)) c c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull (wOver (𝟙 Y))) (pairRes _ Y.hom) (pairIdTrans Y.left) (fun _ _ ↦ rfl) c

theorem isPullO_sub {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
    {h : φ ≫ s = s' ≫ spMap (RingHom.id R)} {a b : HO1 s} {a' b' : HO1 s'} (ha : IsPullO h a a')
    (hb : IsPullO h b b') : IsPullO h (a - b) (a' - b') := by
  unfold IsPullO at *; rw [map_sub, map_sub, ha, hb]

theorem eq_zero_of_isAffine {X : Scheme.{0}} [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s) : c = 0 :=
  H1.eq_zero_of_isInitial (OAff s) (T₀ := op ⟨⊤, isAffineOpen_top _⟩)
    (Limits.IsInitial.ofUniqueHom (fun U ↦ (homOfLE (le_top (a := U.unop.1))).op) fun _ _ ↦ rfl) c

theorem isPullO_through_unit {Y Z : Over (Sp R)} (g : Y ⟶ 𝟙_ (Over (Sp R))) (e : 𝟙_ (Over (Sp R)) ⟶ Z)
    (c : HO1 Z.hom) : IsPullO (wOver (g ≫ e)) c 0 := by
  have : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))
  obtain ⟨c', hc', -⟩ := existsUnique_isPullO (wOver e) c
  rw [eq_zero_of_isAffine _ c'] at hc'
  exact isPullO_over_comp g e hc' ((map_zero _).trans (map_zero _).symm)

variable (A : Over (Sp R)) [GrpObj A]

theorem primitive_structure_sheaf_cohomology_class
    (hAx : ∀ c : HO1 (A ⊗ A).hom, IsPullO (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0 →
      IsPullO (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0 → c = 0) (c : HO1 A.hom) :
    pullHO1 (wOver μ[A]) c = pullHO1 (wOver (fst A A)) c + pullHO1 (wOver (snd A A)) c := by
  have one_def : (1 : A ⟶ A) = toUnit A ≫ η[A] := rfl
  have key : ∀ (f : A ⟶ A ⊗ A) {a b : HO1 A.hom}, f ≫ μ[A] = 𝟙 A →
      IsPullO (wOver (f ≫ fst A A)) c a → IsPullO (wOver (f ≫ snd A A)) c b → c - a - b = 0 →
      IsPullO (wOver f) (pullHO1 (wOver μ[A]) c - pullHO1 (wOver (fst A A)) c - pullHO1 (wOver (snd A A)) c) 0 := by
    intro f a b hμ ha hb hab
    have hcomp : ∀ (g : A ⊗ A ⟶ A) {w : HO1 A.hom}, IsPullO (wOver (f ≫ g)) c w →
        IsPullO (wOver f) (pullHO1 (wOver g) c) w := fun g w hw ↦ by
      have h1 := isPullO_pullHO1 (wOver f) (pullHO1 (wOver g) c)
      have h2 := isPullO_over_comp f g (isPullO_pullHO1 (wOver g) c) h1
      rwa [hw.eq_pullHO1.trans h2.eq_pullHO1.symm]
    have h0 : IsPullO (wOver (f ≫ μ[A])) c c := by rw [hμ]; exact isPullO_over_id _ c
    have := isPullO_sub (isPullO_sub (hcomp μ[A] h0) (hcomp (fst A A) ha)) (hcomp (snd A A) hb)
    rwa [hab] at this
  have z1 := key (lift (𝟙 A) (1 : A ⟶ A)) (a := c) (b := 0) (by rw [← Hom.mul_def, _root_.mul_one])
    (by rw [lift_fst]; exact isPullO_over_id _ c)
    (by rw [lift_snd, one_def]; exact isPullO_through_unit _ _ c) (by simp)
  have z2 := key (lift (1 : A ⟶ A) (𝟙 A)) (a := 0) (b := c) (by rw [← Hom.mul_def, _root_.one_mul])
    (by rw [lift_fst, one_def]; exact isPullO_through_unit _ _ c)
    (by rw [lift_snd]; exact isPullO_over_id _ c) (by simp)
  exact sub_eq_zero.1 ((sub_sub _ _ _).symm.trans (hAx _ z1 z2))
end Over

section Lift
variable {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
  {C D : Type} [Category.{0} C] [Category.{0} D]

def pairFn (φ : X' ⟶ X) (u : C ⥤ AffOp X) (t : D ⥤ C) (fb : D ⥤ AffOp X')
    (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) : D ⥤ (Pair φ)ᵒᵖ where
  obj d := op ⟨((fb.obj d).unop, (u.obj (t.obj d)).unop), hle d⟩
  map {d d'} a := (homOfLE (show (⟨((fb.obj d').unop, (u.obj (t.obj d')).unop), hle d'⟩ : Pair φ) ≤
    ⟨((fb.obj d).unop, (u.obj (t.obj d)).unop), hle d⟩ from
    Prod.le_def.2 ⟨leOfHom (fb.map a).unop, leOfHom (u.map (t.map a)).unop⟩)).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def liftAlong (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (u : C ⥤ AffOp X) (t : D ⥤ C) (fb : D ⥤ AffOp X')
    (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) :
    CoefMap (RingHom.id R) (u ⋙ OAff s) (fb ⋙ OAff s') where
  G := t
  α d := (pairPull h).α ((pairFn φ u t fb hle).obj d)
  naturality a b := (pairPull h).naturality ((pairFn φ u t fb hle).map a) b
  smul d := (pairPull h).smul ((pairFn φ u t fb hle).obj d)

theorem liftAlong_pull1 (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (u : C ⥤ AffOp X) (t : D ⥤ C)
    (fb : D ⥤ AffOp X') (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) (c : HO1 s) :
    (liftAlong h u t fb hle).pull1 ((CoefMap.restrict (OAff s) u).pull1 c) =
      (CoefMap.restrict (OAff s') fb).pull1 (pullHO1 h c) := by
  let r : CoefMap (RingHom.id R) (OPair φ s') (fb ⋙ OAff s') :=
    { G := pairFn φ u t fb hle, α _ := RingHom.id _, naturality _ _ := rfl, smul _ _ _ := rfl }
  have t1 : (liftAlong h u t fb hle).pull1 ((CoefMap.restrict (OAff s) u).pull1 c) =
      r.pull1 ((pairPull h).pull1 c) := by obtain ⟨f, rfl⟩ := H1.mk_surjective _ c; rfl
  have t2 : ∀ x : HO1 s', r.pull1 ((pairRes φ s').pull1 x) = (CoefMap.restrict (OAff s') fb).pull1 x := fun x ↦ by
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ x; rfl
  rw [t1, (isPullO_pullHO1 h c : _ = _), t2]
end Lift

theorem aff_inf_preimage {X Y T : Scheme.{0}} (s : Y ⟶ T) [IsSeparated s] [IsAffine T] (f : X ⟶ Y) {V : X.Opens}
    (hV : IsAffineOpen V) {U : Y.Opens} (hU : IsAffineOpen U) : IsAffineOpen (V ⊓ f ⁻¹ᵁ U) := by
  have : IsAffine V := hV
  have : IsAffineHom ((V.ι ≫ f) ≫ s) := inferInstance
  have : IsAffineHom (V.ι ≫ f) := IsAffineHom.of_comp _ s
  have := (hU.preimage (V.ι ≫ f)).image_of_isOpenImmersion V.ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at this

section Main
variable (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)

def Vop (a b : P) : (A ⊗ A).left.Opens := (fst A A).left ⁻¹ᵁ (S.u a).1 ⊓ (snd A A).left ⁻¹ᵁ (S.u b).1

def Wop (a b c : P) : (A ⊗ A).left.Opens := Vop A S a b ⊓ μ[A].left ⁻¹ᵁ (S.u c).1

theorem Vop_aff (a b : P) : IsAffineOpen (Vop A S a b) := (kunneth_open A A (S.u a) (S.u b)).choose

theorem Wop_aff [IsSeparated A.hom] (a b c : P) : IsAffineOpen (Wop A S a b c) :=
  aff_inf_preimage A.hom _ (Vop_aff A S a b) (S.u c).2

theorem Wop_mono {a a' b b' c c' : P} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    Wop A S a' b' c' ≤ Wop A S a b c := fun _ hx ↦
  ⟨⟨S.mono ha hx.1.1, S.mono hb hx.1.2⟩, S.mono hc hx.2⟩

variable [IsSeparated A.hom]

def wFn : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ ⥤ AffOp (A ⊗ A).left where
  obj T := op ⟨Wop A S T.1.1.unop T.1.2.unop T.2.unop, Wop_aff A S _ _ _⟩
  map {T T'} f := (homOfLE (show (⟨Wop A S T'.1.1.unop T'.1.2.unop T'.2.unop, Wop_aff A S _ _ _⟩ :
      (A ⊗ A).left.affineOpens) ≤ ⟨Wop A S T.1.1.unop T.1.2.unop T.2.unop, Wop_aff A S _ _ _⟩ from
    Wop_mono A S (leOfHom f.1.1.unop) (leOfHom f.1.2.unop) (leOfHom f.2.unop))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

abbrev GG : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ ⥤ CommAlgCat.{0} R := wFn A S ⋙ OAff (A ⊗ A).hom

def pMap : CoefMap (RingHom.id R) (OSys A.hom S) (GG A S) :=
  liftAlong (wOver (fst A A)) S.fn (CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.fst _ _) (wFn A S)
    fun _ _ hx ↦ hx.1.1

def qMap : CoefMap (RingHom.id R) (OSys A.hom S) (GG A S) :=
  liftAlong (wOver (snd A A)) S.fn (CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.snd _ _) (wFn A S)
    fun _ _ hx ↦ hx.1.2

def mMap : CoefMap (RingHom.id R) (OSys A.hom S) (GG A S) :=
  liftAlong (wOver μ[A]) S.fn (CategoryTheory.Prod.snd _ _) (wFn A S) fun _ _ hx ↦ hx.2

end Main

def toAlg {C D : Type} [Category.{0} C] [Category.{0} D] {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (T : D) : F.obj (m.G.obj T) →ₐ[R] G.obj T :=
  { m.α T with
    commutes' := fun r ↦ by
      change m.α T _ = _
      rw [Algebra.algebraMap_eq_smul_one, m.smul, map_one, ← Algebra.algebraMap_eq_smul_one]; rfl }

section Main2
variable (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P) [IsSeparated A.hom]

def pA (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) : (OSys A.hom S).obj T.1.1 →ₐ[R] (GG A S).obj T := toAlg (pMap A S) T

def qA (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) : (OSys A.hom S).obj T.1.2 →ₐ[R] (GG A S).obj T := toAlg (qMap A S) T

def pjAlg (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) : (box (OSys A.hom S)).obj T.1 →ₐ[R] (GG A S).obj T :=
  Algebra.TensorProduct.lift (pA A S T) (qA A S T) fun _ _ ↦ Commute.all _ _

theorem pjAlg_tmul (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) (x : (OSys A.hom S).obj T.1.1) (y : (OSys A.hom S).obj T.1.2) :
    pjAlg A S T (x ⊗ₜ[R] y) = pA A S T x * qA A S T y :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

def pj : Proj (box (OSys A.hom S)) (GG A S) where
  α T := pjAlg A S T
  naturality {T T'} φ b := by
    have e : (pjAlg A S T').comp (mp (box (OSys A.hom S)) φ.1) = (mp (GG A S) φ).comp (pjAlg A S T) :=
      Algebra.TensorProduct.ext' fun x y ↦ by
        change pjAlg A S T' (mp (OSys A.hom S) φ.1.1 x ⊗ₜ[R] mp (OSys A.hom S) φ.1.2 y) =
          mp (GG A S) φ (pjAlg A S T (x ⊗ₜ[R] y))
        rw [pjAlg_tmul, pjAlg_tmul, map_mul]
        exact congrArg₂ (· * ·) ((pMap A S).naturality φ x) ((qMap A S).naturality φ y)
    exact congrArg (fun t ↦ t b) e

end Main2

section Main3
variable (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)

def kap (a b : P) : Sec A.hom (S.u a).1 ⊗[R] Sec A.hom (S.u b).1 →ₐ[R] Sec (A ⊗ A).hom (Vop A S a b) :=
  Algebra.TensorProduct.lift (secA (wOver (fst A A)) ⟨(⟨_, Vop_aff A S a b⟩, S.u a), inf_le_left⟩)
    (secA (wOver (snd A A)) ⟨(⟨_, Vop_aff A S a b⟩, S.u b), inf_le_right⟩) fun _ _ ↦ Commute.all _ _

theorem kap_bijective (a b : P) : Function.Bijective (kap A S a b) :=
  (kunneth_open A A (S.u a) (S.u b)).choose_spec

variable [IsSeparated A.hom]

theorem pjAlg_apply (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ)
    (z : (OSys A.hom S).obj T.1.1 ⊗[R] (OSys A.hom S).obj T.1.2) :
    pjAlg A S T z = Sec.res (A ⊗ A).hom
      (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)
      (kap A S T.1.1.unop T.1.2.unop z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [pjAlg_tmul]
    refine Eq.trans ?_ (congrArg _ (Algebra.TensorProduct.lift_tmul _ _ _ _ _).symm)
    refine Eq.trans ?_ (map_mul _ _ _).symm
    refine congrArg₂ (· * ·) ?_ ?_
    · exact congrArg (fun t ↦ t.hom x) ((fst A A).left.appLE_map (U := (S.u T.1.1.unop).1) (V := Vop A S T.1.1.unop T.1.2.unop) inf_le_left
        (homOfLE (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)).op).symm
    · exact congrArg (fun t ↦ t.hom y) ((snd A A).left.appLE_map (U := (S.u T.1.2.unop).1) (V := Vop A S T.1.1.unop T.1.2.unop) inf_le_right
        (homOfLE (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)).op).symm
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _)).symm)

theorem Wop_inf (a b c c' : P) : Wop A S a b (c ⊓ c') = Wop A S a b c ⊓ Wop A S a b c' :=
  le_antisymm (le_inf (Wop_mono A S le_rfl le_rfl inf_le_left) (Wop_mono A S le_rfl le_rfl inf_le_right))
    fun x hx ↦ ⟨hx.1.1, by change μ[A].left x ∈ (S.u (c ⊓ c')).1; rw [S.map_inf]; exact ⟨hx.1.2, hx.2.2⟩⟩

theorem Wop_iSup (a b : P) : ⨆ c, Wop A S a b c = Vop A S a b :=
  le_antisymm (iSup_le fun _ ↦ inf_le_left) fun x hx ↦ by
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (show μ[A].left x ∈ ⨆ c, (S.u c).1 by rw [S.cover]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, hx, hc⟩

theorem pj_qiso [Finite P] (hF : FubiniSt) (hA : AffAcycSt) : AllQIso (pj A S).coef := by
  have : Quiver.IsThin (Pᵒᵖ × Pᵒᵖ) := fun _ _ ↦ ⟨fun f g ↦ Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  refine hF R (Pᵒᵖ × Pᵒᵖ) (box (OSys A.hom S)) Pᵒᵖ (GG A S) (pj A S) fun T ↦ ?_
  let u : P →o (A ⊗ A).left.affineOpens := ⟨fun c ↦ ⟨Wop A S T.1.unop T.2.unop c, Wop_aff A S _ _ _⟩,
    fun _ _ h ↦ Wop_mono A S le_rfl le_rfl h⟩
  obtain ⟨h1, h2, h3⟩ := hA R (A ⊗ A).left (A ⊗ A).hom ⟨Vop A S T.1.unop T.2.unop, Vop_aff A S _ _⟩ P u
    (fun _ ↦ inf_le_left) (fun c c' ↦ Wop_inf A S _ _ c c') (Wop_iSup A S _ _)
  let aug : Sec (A ⊗ A).hom (Vop A S T.1.unop T.2.unop) →ₗ[R] Cn (u.monotone.functor.op ⋙ OAff (A ⊗ A).hom) 0 :=
    LinearMap.pi fun c ↦ (Sec.res (A ⊗ A).hom (show (u (c.obj (Fin.last 0)).unop).1 ≤ Vop A S T.1.unop T.2.unop from inf_le_left)).toLinearMap
  have hf : ∀ z c, ((pj A S).fib T z) c = aug (kap A S T.1.unop T.2.unop z) c := fun z c ↦
    pjAlg_apply A S (T, c.obj (Fin.last 0)) z
  have hb := kap_bijective A S T.1.unop T.2.unop
  refine ⟨fun x y e ↦ hb.1 (h1 (funext fun c ↦ ((hf x c).symm.trans (congrFun e c)).trans (hf y c))),
    fun y ↦ (h2 y).trans ⟨fun ⟨w, hw⟩ ↦ by obtain ⟨z, rfl⟩ := hb.2 w; exact ⟨z, hw ▸ funext fun c ↦ hf z c⟩,
      fun ⟨z, hz⟩ ↦ ⟨kap A S T.1.unop T.2.unop z, hz ▸ funext fun c ↦ (hf z c).symm⟩⟩, h3⟩
end Main3

section AutomorphyRankFourMain
variable (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P) [IsSeparated A.hom]

theorem pMap_pull1 (x : H1 (OSys A.hom S)) :
    (pMap A S).pull1 x = (pj A S).coef.pull1 ((boxL (OSys A.hom S)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans (pMap A S) ((boxL (OSys A.hom S)).comp (pj A S).coef) { app _ := 𝟙 _ } (fun T b ↦ ?_) x
  erw [mp_id]; refine (pjAlg_tmul A S T b 1).trans ?_; rw [map_one, _root_.mul_one]; rfl

theorem qMap_pull1 (x : H1 (OSys A.hom S)) :
    (qMap A S).pull1 x = (pj A S).coef.pull1 ((boxR (OSys A.hom S)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans (qMap A S) ((boxR (OSys A.hom S)).comp (pj A S).coef) { app _ := 𝟙 _ } (fun T b ↦ ?_) x
  erw [mp_id]; refine (pjAlg_tmul A S T 1 b).trans ?_; rw [map_one, _root_.one_mul]; rfl

theorem primitive
    (hAx : ∀ c : HO1 (A ⊗ A).hom, IsPullO (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0 →
      IsPullO (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0 → c = 0)
    (hs : Function.Surjective (resSys A.hom S).pull1) (c : H1 (OSys A.hom S)) :
    (mMap A S).pull1 c = (pj A S).coef.pull1 ((boxL (OSys A.hom S)).pull1 c + (boxR (OSys A.hom S)).pull1 c) := by
  obtain ⟨c, rfl⟩ := hs c
  rw [map_add (f := _), ← pMap_pull1, ← qMap_pull1]
  have hm : (mMap A S).pull1 ((resSys A.hom S).pull1 c) = _ := liftAlong_pull1 (wOver μ[A]) S.fn _ (wFn A S) _ c
  have hp : (pMap A S).pull1 ((resSys A.hom S).pull1 c) = _ := liftAlong_pull1 (wOver (fst A A)) S.fn _ (wFn A S) _ c
  have hq : (qMap A S).pull1 ((resSys A.hom S).pull1 c) = _ := liftAlong_pull1 (wOver (snd A A)) S.fn _ (wFn A S) _ c
  rw [hm, hp, hq, ← map_add (f := _), primitive_structure_sheaf_cohomology_class A hAx]

theorem exists_unit_mem (hR : IsField R) : ∃ a₀, η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤ := by
  let := hR.toField
  let f : 𝟙_ (Over (Sp R)) ⟶ Over.mk (𝟙 (Sp R)) := Over.homMk (𝟙_ (Over (Sp R))).hom (Category.comp_id _)
  let g : Over.mk (𝟙 (Sp R)) ⟶ 𝟙_ (Over (Sp R)) := toUnit _
  have hfg : f.left ≫ g.left = 𝟙 (𝟙_ (Over (Sp R))).left :=
    congrArg Over.Hom.left (toUnit_unique (f ≫ g) (𝟙 _))
  have hsub : ∀ p q : Sp R, p = q := fun p q ↦ PrimeSpectrum.ext (Ideal.ext fun r ↦ by
    have h0 : ∀ x : Sp R, r ∈ x.asIdeal ↔ r = 0 := fun x ↦ ⟨fun hr ↦ by_contra fun hr0 ↦
      x.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (mul_inv_cancel₀ hr0 ▸ x.asIdeal.mul_mem_right _ hr)),
      fun hr ↦ hr ▸ x.asIdeal.zero_mem⟩
    rw [h0 p, h0 q])
  let p₀ : (𝟙_ (Over (Sp R))).left := g.left ⟨⊥, ⟨fun h ↦ one_ne_zero (Ideal.mem_bot.1 (h ▸ Submodule.mem_top)), fun h ↦ mul_eq_zero.1 h⟩⟩
  obtain ⟨a₀, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show η[A].left p₀ ∈ ⨆ a, (S.u a).1 by rw [S.cover]; trivial)
  refine ⟨a₀, top_le_iff.1 fun x _ ↦ ?_⟩
  have hx : x = p₀ := by
    have e := congrArg g.left (hsub (f.left x) (f.left p₀))
    simpa [← Scheme.Hom.comp_apply, hfg] using e
  rw [hx]; exact ha

theorem appLE_chain {X Y Z : Scheme.{0}} (ψ : X ⟶ Y) (φ : Y ⟶ Z) (χ : X ⟶ Z) (hχ : ψ ≫ φ = χ) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e1 : V ≤ φ ⁻¹ᵁ U) (e2 : W ≤ ψ ⁻¹ᵁ V) (e3 : W ≤ χ ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (ψ.appLE V W e2).hom ((φ.appLE U V e1).hom x) = (χ.appLE U W e3).hom x := by
  subst hχ; exact congrArg (fun t ↦ t.hom x) (Scheme.Hom.appLE_comp_appLE ψ φ U V W e1 e2)

theorem appLE_id {X : Scheme.{0}} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U e).hom x = x := by
  have h : X.presheaf.map (homOfLE e).op = 𝟙 _ := by
    rw [show (homOfLE e).op = 𝟙 (op U) from Subsingleton.elim _ _]; exact X.presheaf.map_id _
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]; erw [h]; rfl

end AutomorphyRankFourMain

section Main5
variable (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P) [IsSeparated A.hom]

abbrev iota : A ⟶ A ⊗ A := lift (1 : A ⟶ A) (𝟙 A)

def tK (a₀ : P) : Pᵒᵖ ⥤ (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ where
  obj b := ((op a₀, b), b)
  map f := ((𝟙 _, f), f)

theorem iota_fst : (iota A).left ≫ (fst A A).left = A.hom ≫ η[A].left :=
  congrArg (fun f ↦ f.left) (lift_fst (1 : A ⟶ A) (𝟙 A))

theorem iota_snd : (iota A).left ≫ (snd A A).left = 𝟙 _ :=
  congrArg (fun f ↦ f.left) (lift_snd (1 : A ⟶ A) (𝟙 A))

theorem iota_mul : (iota A).left ≫ μ[A].left = 𝟙 _ :=
  congrArg (fun f ↦ f.left) ((Hom.mul_def (1 : A ⟶ A) (𝟙 A)).symm.trans (_root_.one_mul (𝟙 A)))

variable {A S}

theorem kle {a₀ : P} (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) :
    (S.fn.obj b).unop.1 ≤ (iota A).left ⁻¹ᵁ ((wFn A S).obj ((tK a₀).obj b)).unop.1 := fun x hx ↦
  ⟨⟨show (fst A A).left ((iota A).left x) ∈ (S.u a₀).1 by
       rw [← Scheme.Hom.comp_apply, iota_fst, Scheme.Hom.comp_apply]
       have h2 : A.hom x ∈ η[A].left ⁻¹ᵁ (S.u a₀).1 := by rw [ha]; trivial
       exact h2,
    show (snd A A).left ((iota A).left x) ∈ (S.u b.unop).1 by rw [← Scheme.Hom.comp_apply, iota_snd]; exact hx⟩,
   show μ[A].left ((iota A).left x) ∈ (S.u b.unop).1 by rw [← Scheme.Hom.comp_apply, iota_mul]; exact hx⟩

def kMap {a₀ : P} (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) : CoefMap (RingHom.id R) (GG A S) (OSys A.hom S) :=
  liftAlong (wOver (iota A)) (wFn A S) (tK a₀) S.fn (kle ha)
end Main5

section Main6
variable {A : Over (Sp R)} [GrpObj A] {P : Type} [SemilatticeInf P] {S : Sys A.left P}
  [IsSeparated A.hom] {a₀ : P}

theorem unit_isAffine : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))

attribute [local instance] unit_isAffine

theorem unit_bijective (R : Type) [CommRing R] : Function.Bijective (algebraMap R (Sec (𝟙_ (Over (Sp R))).hom ⊤)) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

def ptPair (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) : Pair η[A].left := ⟨(⟨⊤, isAffineOpen_top _⟩, S.u a₀), ha.ge⟩

def epsA (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) : (OSys A.hom S).obj (op a₀) →ₐ[R] R :=
  (AlgEquiv.ofBijective (Algebra.ofId R (Sec (𝟙_ (Over (Sp R))).hom ⊤)) (unit_bijective R)).symm.toAlgHom.comp
    (secA (wOver η[A]) (ptPair ha) : Sec A.hom (S.u a₀).1 →ₐ[R] Sec (𝟙_ (Over (Sp R))).hom ⊤)

theorem algebraMap_epsA (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (x : (OSys A.hom S).obj (op a₀)) :
    algebraMap R (Sec (𝟙_ (Over (Sp R))).hom ⊤) (epsA ha x) = secA (wOver η[A]) (ptPair ha) x :=
  (AlgEquiv.ofBijective (Algebra.ofId R (Sec (𝟙_ (Over (Sp R))).hom ⊤)) (unit_bijective R)).apply_symm_apply
    (secA (wOver η[A]) (ptPair ha) x)

theorem kMap_qA (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) (y : (OSys A.hom S).obj b) :
    (kMap ha).α b (qA A S ((tK a₀).obj b) y) = y :=
  (appLE_chain (iota A).left (snd A A).left (𝟙 _) (iota_snd A) _ _ le_rfl y).trans (appLE_id _ _ y)

theorem kMap_mMap (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) (y : (OSys A.hom S).obj b) :
    (kMap ha).α b ((mMap A S).α ((tK a₀).obj b) y) = y :=
  (appLE_chain (iota A).left μ[A].left (𝟙 _) (iota_mul A) _ _ le_rfl y).trans (appLE_id _ _ y)

theorem kMap_pA (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) (x : (OSys A.hom S).obj (op a₀)) :
    (kMap ha).α b (pA A S ((tK a₀).obj b) x) = algebraMap R ((OSys A.hom S).obj b) (epsA ha x) := by
  let tU := secA (wOver (toUnit A)) (⟨(S.u b.unop, ⟨⊤, isAffineOpen_top _⟩), le_top⟩ : Pair (toUnit A).left)
  have h1 : algebraMap R ((OSys A.hom S).obj b) (epsA ha x) = tU (secA (wOver η[A]) (ptPair ha) x) := by
    rw [← algebraMap_epsA]; exact (tU.commutes _).symm
  have hE : ∀ W : A.left.Opens, W ≤ (A.hom ≫ η[A].left) ⁻¹ᵁ (S.u a₀).1 := fun _ x _ ↦ by
    have h2 : A.hom x ∈ η[A].left ⁻¹ᵁ (S.u a₀).1 := by rw [ha]; trivial
    exact h2
  rw [h1]
  exact (appLE_chain (iota A).left (fst A A).left (A.hom ≫ η[A].left) (iota_fst A) _ _ (hE _) x).trans
    (appLE_chain A.hom η[A].left (A.hom ≫ η[A].left) rfl _ _ (hE _) x).symm

theorem evL_eq (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ)
    (z : (OSys A.hom S).obj (op a₀) ⊗[R] (OSys A.hom S).obj b) :
    evL (OSys A.hom S) (op a₀) b (epsA ha) z = (kMap ha).α b (pjAlg A S ((tK a₀).obj b) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg _ (pjAlg_tmul A S ((tK a₀).obj b) x y).symm)
    refine Eq.trans ?_ (map_mul _ _ _).symm
    rw [kMap_pA, kMap_qA]; rfl
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _)).symm)

theorem counit (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (y : H2 (OSys A.hom S)) (w : H2 (box (OSys A.hom S)))
    (e : (pj A S).coef.pull2 w = (mMap A S).pull2 y) :
    (boxE (OSys A.hom S) (op a₀) (epsA ha)).pull2 w = y := by
  have e' := congrArg (kMap ha).pull2 e
  rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp] at e'
  have l1 : ((pj A S).coef.comp (kMap ha)).pull2 w = (boxE (OSys A.hom S) (op a₀) (epsA ha)).pull2 w := by
    let θ : ((pj A S).coef.comp (kMap ha)).G ⟶ (boxE (OSys A.hom S) (op a₀) (epsA ha)).G :=
      { app := fun b ↦ 𝟙 ((CategoryTheory.Prod.sectR (op a₀) Pᵒᵖ).obj b)
        naturality := fun _ _ _ ↦ Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _) }
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans ((pj A S).coef.comp (kMap ha)) (boxE (OSys A.hom S) (op a₀) (epsA ha)) θ
      (fun b z ↦ by erw [mp_id]; exact evL_eq ha b z) w
  have l2 : ((mMap A S).comp (kMap ha)).pull2 y = (CoefMap.id (OSys A.hom S)).pull2 y := by
    let θ : ((mMap A S).comp (kMap ha)).G ⟶ (CoefMap.id (OSys A.hom S)).G :=
      { app := fun b ↦ 𝟙 b, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ (fun b z ↦ by erw [mp_id]; exact (kMap_mMap ha b z).symm) y
  rw [← l1, e', l2, CoefMap.pullCohomologyTwo_id]
end Main6

theorem hopfSt : HtpySt → QCalcSt → FubiniSt → AffAcycSt → DescentSt → LowSt → AxOSt → HopfSt := by
  intro _ _ hF hA hD hL hX R _ A _ g hab hsm P _ _ S
  have := hab.proper
  have : IsSeparated A.hom := inferInstance
  refine ⟨(Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ, inferInstance, GG A S, (pj A S).coef, mMap A S, pj_qiso A S hF hA,
    primitive A S (hX R A g hab hsm) (hL R _ _ _ _ (resSys A.hom S) (hD R A.left A.hom inferInstance P S)).1.2, fun hR ↦ ?_⟩
  obtain ⟨a₀, ha⟩ := exists_unit_mem A S hR
  exact ⟨op a₀, epsA ha, fun y w e ↦ counit ha y w e⟩
end GlobalTheory.CompanionTheory.HopfSys
