module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EqOfUnitGlobalSectionEq
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitEqMultiplicativeGroupSection
public import Development.AutomorphicArithmetic.CommutativeAlgebra.KummerClassAddOfUnitSecAdd
public import Development.AutomorphicArithmetic.CommutativeAlgebra.KumSExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.PicUnit
import Mathlib.Tactic.Linter.Style

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.KumRoot

private alias map_res := _root_.GlobalTheory.EtC.exactIff_map_res

private alias res_comp := _root_.GlobalTheory.EtC.ClsSpec.res_comp

private alias sec_map_sub := _root_.GlobalTheory.EtC.KummerSplit.smap_sub

private alias sec_res_add := _root_.GlobalTheory.TwSec.res_add

private alias sec_res_nsmul := _root_.GlobalTheory.TwSec.res_nsmul

private lemma map_smul_int {V : Scheme.{0}} (b : Sec Gm V) (n : ℤ) : Sec.map (n • 𝟙 Gm) b = n • b := by
  rfl

private alias unitSec_pow := _root_.GlobalTheory.EtC.KummerSeq.unitSec_pow

variable (q : ℕ) [NeZero q]

private noncomputable def kp {V : Scheme.{0}} (s : Sec (tw q 1) V) : Sec Gm V :=
  Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from s)

private lemma kp_add {V : Scheme.{0}} (s t : Sec (tw q 1) V) : kp q (s + t) = kp q s + kp q t := by
  unfold kp
  exact _root_.GlobalTheory.EtC.ClsSpec.smap_add _ _ _

private lemma kp_res {W V : Scheme.{0}} (k : W ⟶ V) (s : Sec (tw q 1) V) :
    Sec.res k (kp q s) = kp q (Sec.res k s) := by
  unfold kp
  exact (map_res _ _ _).symm

private lemma kp_nsmul {V : Scheme.{0}} (s : Sec (tw q 1) V) : q • kp q s = 0 := by
  unfold kp
  have h0 := (UpperTheory.Deg2.kap_spec q).2.1
  have h1 : Sec.map ((q : ℤ) • 𝟙 Gm) (Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from s)) =
      Sec.map (UpperTheory.Deg2.kap q ≫ ((q : ℤ) • 𝟙 Gm)) (show Sec (UpperTheory.Deg2.T q) V from s) := rfl
  rw [← natCast_zsmul, ← map_smul_int, h1, h0]
  rfl

private lemma unique_datum {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (v v' : (Γ(V, ⊤))ˣ)
    (s s' : Sec (tw q 1) V) (hv : v ^ q = v' ^ q)
    (h : kumT q V v + Sec.map (resι _ (tw q 1)) s = kumT q V v' + Sec.map (resι _ (tw q 1)) s') :
    unitSec v + kp q s = unitSec v' + kp q s' := by
  have hx : Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec (v⁻¹ * v')) = 0 := by
    rw [map_smul_int, natCast_zsmul, ← unitSec_pow, mul_pow, ← hv, inv_pow, inv_mul_cancel,
      UpperTheory.PicD.unitSec_one]
  obtain ⟨a, ha⟩ := (UpperTheory.Deg2.kap_spec q).2.2.2.1 V hq (unitSec (v⁻¹ * v')) hx
  have e1 : unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) a := by
    rw [ha, ← UpperTheory.PicD.unitSec_mul, mul_inv_cancel_left]
  have e2 := UpperTheory.kummer_class_add_of_unitSec_add q V hq v v' a e1
  rw [e2, add_assoc] at h
  have h3 : Sec.map (resι _ (tw q 1)) s = Sec.map (resι _ (tw q 1)) ((show Sec (tw q 1) V from a) + s') := by
    rw [_root_.GlobalTheory.EtC.ClsSpec.smap_add]
    exact add_left_cancel h
  have hs := (_root_.GlobalTheory.EtC.resSec _ _ V).2.1 h3
  rw [hs, kp_add, e1, add_assoc]
  rfl

end UpperTheory.KumRoot

open UpperTheory.KumRoot in
theorem UpperTheory.exists_root_of_kummer_class_eq_zero :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (w : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q w = 0 → ∃ v : (Γ(X, ⊤))ˣ, v ^ q = w := by
  intro q _ X w hq hw
  obtain ⟨γ, hγ, -, hγ2⟩ := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).1 X w hq
  rw [hw] at hγ
  obtain ⟨y, hy⟩ := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff (ZMod q) X (res (ZMod q) (tw q 1)) 0 1 2 (by norm_num) (by norm_num)).2 γ).2.1 hγ
  have hqV : ∀ {V : Scheme.{0}} (g : V ⟶ X), IsUnit (q : Γ(V, ⊤)) := by
    intro V g
    have := hq.map g.appTop.hom
    simpa using this
  let D : (V : Scheme.{0}) → (V ⟶ X) → Sec Gm V → Prop := fun V g b =>
    ∃ (v : (Γ(V, ⊤))ˣ) (s : Sec (tw q 1) V),
      v ^ q = Units.map ↑(CommRingCat.Hom.hom (Scheme.Hom.appTop g)) w ∧
      Sec.res g y = kumT q V v + Sec.map (resι _ (tw q 1)) s ∧ b = unitSec v + kp q s
  have hA : ∀ {V : Scheme.{0}} (g : V ⟶ X) (v : (Γ(V, ⊤))ˣ),
      v ^ q = Units.map ↑(CommRingCat.Hom.hom (Scheme.Hom.appTop g)) w → ∃ b, D V g b := by
    intro V g v hv
    have e := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q) (E := sch.obj X) (I := res (ZMod q) (tw q 1)) (n := 1)).2.1
      (γ : Cochain _ _ 1) 0 1 (by norm_num) V X g (𝟙 X)
    have hd : Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (Sec.res g y - kumT q V v) = 0 := by
      rw [sec_map_sub, map_res, hy, sub_eq_zero]
      refine e.trans ?_
      exact hγ2 V g v hv
    obtain ⟨s, hs⟩ := ((_root_.GlobalTheory.EtC.resSec _ _ V).1 _).1 hd
    exact ⟨_, v, s, hv, by rw [hs]; abel, rfl⟩
  have hB : ∀ {V : Scheme.{0}} (g : V ⟶ X) (b b' : Sec Gm V), D V g b → D V g b' → b = b' := by
    intro V g b b' ⟨v, s, hv, hs, hb⟩ ⟨v', s', hv', hs', hb'⟩
    rw [hb, hb']
    exact unique_datum q (hqV g) v v' s s' (hv.trans hv'.symm) (hs.symm.trans hs')
  have hC : ∀ {V W : Scheme.{0}} (g : V ⟶ X) (k : W ⟶ V) (b : Sec Gm V), D V g b → D W (k ≫ g) (Sec.res k b) := by
    intro V W g k b ⟨v, s, hv, hs, hb⟩
    refine ⟨Units.map ↑(CommRingCat.Hom.hom (Scheme.Hom.appTop k)) v, Sec.res k s, ?_, ?_, ?_⟩
    · rw [← map_pow, hv]
      exact (_root_.GlobalTheory.EtC.ClsSpec.umap_comp k g w).symm
    · rw [← res_comp, hs, sec_res_add, (_root_.GlobalTheory.EtC.KummerSplit.isKum_kumT q).1 W V k v (hqV g), map_res]
      rfl
    · rw [hb, sec_res_add, UpperTheory.PicD.unitSec_res, kp_res]
      rfl
  have hloc : Loc X fun V g => ∃ b, D V g b :=
    GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 X _ _ ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q X).2.2.2 hq w) (fun V g ⟨v, hv⟩ => hA g v hv)
  obtain ⟨S, hS, hSP⟩ := hloc
  obtain ⟨b0, hb0⟩ := (_root_.GlobalTheory.EtC.sec_ext_glue ℤ Gm X).2 S hS (fun V g hg => Classical.choose (hSP V g hg))
    (fun V W g k hg => hB (k ≫ g) _ _ (hC g k _ (Classical.choose_spec (hSP V g hg)))
      (Classical.choose_spec (hSP W (k ≫ g) (S.downward_closed hg k))))
  obtain ⟨u, hu⟩ := UpperTheory.exists_unit_eq_multiplicativeGroup_section X b0
  refine ⟨u, UpperTheory.eq_of_unitGlobalSection_eq X _ _ ?_⟩
  rw [unitSec_pow, hu]
  apply (_root_.GlobalTheory.EtC.sec_ext_glue ℤ Gm X).1
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨v, s, hv, -, hb⟩ := Classical.choose_spec (hSP V g hg)
  rw [sec_res_nsmul, hb0 V g hg, hb, nsmul_add, kp_nsmul, add_zero, ← unitSec_pow, hv,
    UpperTheory.PicD.unitSec_res]
  rfl
