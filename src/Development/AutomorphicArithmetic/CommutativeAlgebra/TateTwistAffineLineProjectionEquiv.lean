module

public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.InjectiveComplexProductSectionMapQuasiIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtaleStatement
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.AffineEquivalences

variable {R : Type} [CommRing R]

private alias res_comp := _root_.GlobalTheory.TwSec.res_comp

private alias res_id := _root_.GlobalTheory.EtC.ClsSpec.res_id

private alias map_res := _root_.GlobalTheory.EtC.exactIff_map_res

private alias res_zero := _root_.GlobalTheory.TwSec.res_zero

private alias res_add := _root_.GlobalTheory.TwSec.res_add

private theorem ev_pull {Y X : Scheme.{0}} (π : Y ⟶ X) (I : Cx R) (n : ℤ) (α : Cochain ((chains R).obj (sch.obj X)) I n) :
    ev ((Cochain.ofHom ((chains R).map (sch.map π))).comp α (zero_add n)) 0 n (by simp) Y (𝟙 Y) =
      Sec.res π (ev α 0 n (by simp) X (𝟙 X)) := by
  have hev := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)
  rw [hev.2.2.2.1 (sch.map π) α 0 n (by simp) Y (𝟙 Y), hev.2.1 α 0 n (by simp) Y X π (𝟙 X)]
  congr 1

private theorem sec_surj {Y X : Scheme.{0}} (π : Y ⟶ X) (F : Shv R) (hE : Eqv R (sch.map π) F) (n : ℤ)
    (b : Sec ((res R F).X n) Y) (hb : Sec.map ((res R F).d n (n + 1)) b = 0) :
    ∃ (a : Sec ((res R F).X n) X) (c : Sec ((res R F).X (n - 1)) Y),
      Sec.map ((res R F).d n (n + 1)) a = 0 ∧ Sec.res π a = b + Sec.map ((res R F).d (n - 1) n) c := by
  have hY := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R Y (res R F) (n - 1) n (n + 1) (by ring) rfl
  have hX := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (n - 1) n (n + 1) (by ring) rfl
  have hevY := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj Y) (I := res R F) (n := n)
  obtain ⟨β, hβ, -⟩ := hY.1 b hb
  obtain ⟨x, hx⟩ := (hE n).2 (CohomologyClass.mk β)
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have hx' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map π))) α (zero_add n)) = CohomologyClass.mk β := hx
  have h0 : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map π))) α (zero_add n) - β) = 0 := by
    rw [CohomologyClass.mk_sub, hx', sub_self]
  obtain ⟨y, hy⟩ := ((hY.2 _).2).1 h0
  refine ⟨ev α.1 0 n (by simp) X (𝟙 X), y, (hX.2 α).1, ?_⟩
  rw [hy]
  have e1 : ev (zcomp (Cocycle.ofHom ((chains R).map (sch.map π))) α (zero_add n) - β).1 0 n (by simp) Y (𝟙 Y) =
      Sec.res π (ev α.1 0 n (by simp) X (𝟙 X)) - ev β.1 0 n (by simp) Y (𝟙 Y) := by
    rw [← ev_pull π (res R F) n α.1]
    exact (hevY.1 _ _ 0 n (by simp) Y (𝟙 Y)).2.1
  rw [e1, hβ Y (𝟙 Y), res_id]
  abel

private theorem sec_inj {Y X : Scheme.{0}} (π : Y ⟶ X) (F : Shv R) (hE : Eqv R (sch.map π) F) (n : ℤ)
    (a : Sec ((res R F).X n) X) (ha : Sec.map ((res R F).d n (n + 1)) a = 0)
    (hc : ∃ c : Sec ((res R F).X (n - 1)) Y, Sec.res π a = Sec.map ((res R F).d (n - 1) n) c) :
    ∃ a' : Sec ((res R F).X (n - 1)) X, Sec.map ((res R F).d (n - 1) n) a' = a := by
  have hY := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R Y (res R F) (n - 1) n (n + 1) (by ring) rfl
  have hX := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (n - 1) n (n + 1) (by ring) rfl
  obtain ⟨α, hα, -⟩ := hX.1 a ha
  obtain ⟨c, hc⟩ := hc
  have h0 : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map π))) α (zero_add n)) = 0 := by
    refine ((hY.2 _).2).2 ⟨c, ?_⟩
    have := ev_pull π (res R F) n α.1
    rw [hα X (𝟙 X), res_id] at this
    exact hc.symm.trans this.symm
  have h1 : CohomologyClass.mk α = 0 := (hE n).1 (by
    rw [map_zero]
    exact h0)
  obtain ⟨y, hy⟩ := ((hX.2 α).2).1 h1
  refine ⟨y, ?_⟩
  rw [hy, hα X (𝟙 X), res_id]

private theorem loc_affine (T : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop)
    (hres : ∀ {W V : Scheme.{0}} (h : W ⟶ T) (f : V ⟶ W), P W h → P V (f ≫ h))
    (haff : ∀ (W : Scheme.{0}) [IsAffine W] (h : W ⟶ T), P W h) : Loc T P := by
  refine ⟨Sieve.generate (fun W h => IsAffine W), ?_, ?_⟩
  · apply Scheme.zariskiTopology_le_etaleTopology
    refine GrothendieckTopology.superset_covering _ ?_ T.affineCover.mem_grothendieckTopology
    rintro V g ⟨W, f, h, ⟨i⟩, rfl⟩
    exact ⟨_, f, _, inferInstanceAs (IsAffine (T.affineCover.X i)), rfl⟩
  · rintro V g ⟨W, f, h, hW, rfl⟩
    haveI : IsAffine W := hW
    exact hres h f (haff W h)

open Polynomial in
private theorem line_iso (A : Type) [CommRing A] :
    ∃ u : Spec (CommRingCat.of A[X]) ⟶ Pbf.A1 ⨯ Spec (CommRingCat.of A), IsIso u ∧
      u ≫ prod.snd = Spec.map (CommRingCat.ofHom (C : A →+* A[X])) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (_root_.GlobalTheory.PolynomialPushoutEquivalence.isPushout_poly (Int.castRingHom A))
  refine ⟨prod.lift (Spec.map (CommRingCat.ofHom (mapRingHom (Int.castRingHom A))))
    (Spec.map (CommRingCat.ofHom (C : A →+* A[X]))), ⟨sq.lift prod.fst prod.snd (specZIsTerminal.hom_ext _ _), ?_, ?_⟩, prod.lift_snd _ _⟩
  · apply sq.hom_ext
    · rw [Category.assoc, IsPullback.lift_fst, prod.lift_fst, Category.id_comp]
    · rw [Category.assoc, IsPullback.lift_snd, prod.lift_snd, Category.id_comp]
  · apply Limits.prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, IsPullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, prod.lift_snd, IsPullback.lift_snd, Category.id_comp]

open Polynomial in
private theorem eqv_spec (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hq : IsUnit (q : A)) (i : ℤ) :
    Eqv _ (sch.map (prod.snd : Pbf.A1 ⨯ Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))) (tw q i) := by
  obtain ⟨u, hu, hc⟩ := line_iso A
  have h := _root_.GlobalTheory.T.homotopy_invariance_etale_alt q A hq i
  have h' : Eqv _ (sch.map u ≫ sch.map (prod.snd : Pbf.A1 ⨯ Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))) (tw q i) := by
    rw [← Functor.map_comp, hc]
    exact h
  exact ((_root_.GlobalTheory.EtC.eqv_basic _ _).2.1 _ _ _ _ _).2.1
    (_root_.GlobalTheory.EtC.eqv_of_isIso _ _) h'

private theorem eqv_aff (q : ℕ) [NeZero q] (W : Scheme.{0}) [IsAffine W] (hq : IsUnit (q : Γ(W, ⊤))) (i : ℤ) :
    Eqv _ (sch.map (prod.snd : Pbf.A1 ⨯ W ⟶ W)) (tw q i) := by
  have h : Eqv _ (sch.map (prod.snd : Pbf.A1 ⨯ Spec Γ(W, ⊤) ⟶ Spec Γ(W, ⊤))) (tw q i) := eqv_spec q Γ(W, ⊤) hq i
  have h' : sch.map (prod.snd : Pbf.A1 ⨯ W ⟶ W) ≫ sch.map W.isoSpec.hom =
      sch.map (prod.map (𝟙 Pbf.A1) W.isoSpec.hom) ≫ sch.map (prod.snd : Pbf.A1 ⨯ Spec Γ(W, ⊤) ⟶ Spec Γ(W, ⊤)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, prod.map_snd]
  refine ((_root_.GlobalTheory.EtC.eqv_basic _ _).2.1 _ _ _ _ (sch.map W.isoSpec.hom)).2.2
    (_root_.GlobalTheory.EtC.eqv_of_isIso _ _) ?_
  rw [h']
  exact ((_root_.GlobalTheory.EtC.eqv_basic _ _).2.1 _ _ _ _ _).1
    (_root_.GlobalTheory.EtC.eqv_of_isIso _ _) h

private noncomputable def psi {R : Type} [CommRing R] (F : Shv R) (T : Scheme.{0}) : Sec F T →+ Sec F (Pbf.A1 ⨯ T) :=
  ((F.obj.map (prod.snd : Pbf.A1 ⨯ T ⟶ T).op).hom).toAddMonoidHom

private theorem psi_apply {R : Type} [CommRing R] (F : Shv R) (T : Scheme.{0}) (a : Sec F T) :
    psi F T a = Sec.res prod.snd a := rfl

private theorem res_psi {F : Shv R} {T' T : Scheme.{0}} (g : T' ⟶ T) (a : Sec F T) :
    Sec.res (prod.map (𝟙 Pbf.A1) g) (psi F T a) = psi F T' (Sec.res g a) := by
  rw [psi_apply, psi_apply, ← res_comp, ← res_comp, prod.map_snd]

private theorem res_prod {F : Shv R} {V W T : Scheme.{0}} (f : V ⟶ W) (h : W ⟶ T) (a : Sec F (Pbf.A1 ⨯ T)) :
    Sec.res (prod.map (𝟙 Pbf.A1) (f ≫ h)) a = Sec.res (prod.map (𝟙 Pbf.A1) f) (Sec.res (prod.map (𝟙 Pbf.A1) h) a) := by
  rw [← res_comp]
  congr 1
  simp

end UpperTheory.AffineEquivalences

open UpperTheory.AffineEquivalences in
theorem UpperTheory.tateTwist_affineLine_projection_equiv :
    ∀ (q : ℕ) [NeZero q] (E : Spc) (i : ℤ), Inv q E → Eqv _ (prod.snd : sch.obj A1 ⨯ E ⟶ E) (tw q i) := by
  intro q _ E i hE
  obtain ⟨-, hinj, hge, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (tw q i)
  haveI := hge
  have hZ : ∀ {T' T : Scheme.{0}}, (T' ⟶ T) → IsUnit (q : Γ(T, ⊤)) → IsUnit (q : Γ(T', ⊤)) := fun g h => by
    simpa using h.map g.appTop.hom
  obtain ⟨Φ, hΦ, hform⟩ := UpperTheory.injectiveComplex_productSection_map_quasiIso (ZMod q) Pbf.A1 (res _ (tw q i)) (res _ (tw q i)) hinj hinj
    (fun T s => psi _ T) (fun g s a => res_psi g a)
    (fun T s t a => map_res _ _ a) (fun T => IsUnit (q : Γ(T, ⊤))) hZ
    (by
      intro T hT n b hb
      refine loc_affine T _ ?_ ?_
      · rintro W V h f ⟨a, c, ha, hac⟩
        refine ⟨Sec.res f a, Sec.res (prod.map (𝟙 Pbf.A1) f) c, ?_, ?_⟩
        · rw [map_res, ha, res_zero]
        · rw [← res_psi, hac, map_res, res_prod, res_add]
      · intro W _ h
        obtain ⟨a, c, ha, hac⟩ := sec_surj (prod.snd : Pbf.A1 ⨯ W ⟶ W) (tw q i) (eqv_aff q W (hZ h hT) i) n
          (Sec.res (prod.map (𝟙 Pbf.A1) h) b) (by rw [map_res, hb, res_zero])
        exact ⟨a, c, ha, hac⟩)
    (by
      intro T hT n a ha hc
      refine loc_affine T _ ?_ ?_
      · rintro W V h f ⟨a', ha'⟩
        refine ⟨Sec.res f a', ?_⟩
        rw [map_res, ha', res_comp]
      · intro W _ h
        obtain ⟨c, hc⟩ := hc
        exact sec_inj (prod.snd : Pbf.A1 ⨯ W ⟶ W) (tw q i) (eqv_aff q W (hZ h hT) i) n (Sec.res h a)
          (by rw [map_res, ha, res_zero])
          ⟨Sec.res (prod.map (𝟙 Pbf.A1) h) c, by
            rw [map_res, ← hc]
            exact (res_psi h a).symm⟩)
    E hE
  intro n
  have e : (⇑(pull (ZMod q) (prod.snd : sch.obj Pbf.A1 ⨯ E ⟶ E) (tw q i) n)) = ⇑(Φ n) := by
    funext x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ, hev⟩ := hform n α
    rw [hβ]
    refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    have hb := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q) (E := sch.obj Pbf.A1 ⨯ E) (I := res _ (tw q i)) (n := n)
    have ha := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q) (E := E) (I := res _ (tw q i)) (n := n)
    refine hb.2.2.1 _ _ fun p s h T y => ?_
    rw [hev p s h T y, psi_apply, ← res_comp, prod.lift_snd, res_id]
    exact ha.2.2.2.1 prod.snd α.1 p s h T y
  rw [e]
  exact hΦ n
