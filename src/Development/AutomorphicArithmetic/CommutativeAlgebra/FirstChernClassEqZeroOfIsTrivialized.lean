module

public import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
import Mathlib.Tactic.Linter.Style

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

noncomputable section

namespace UpperTheory.ChernClassOfTrivializedBundle

section Res
variable {R : Type} [CommRing R] {F G : Shv R}

private theorem smap_neg (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map φ (-a) = - Sec.map φ a := map_neg (φ.hom.app (op U)).hom a

private theorem glue {U : Scheme.{0}} (P : ∀ (V : Scheme.{0}) (_ : V ⟶ U), Sec F V → Prop)
    (hex : Loc U fun V g => ∃ a, P V g a)
    (hres : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) a, P V g a → P W (k ≫ g) (Sec.res k a))
    (huniq : ∀ (V : Scheme.{0}) (g : V ⟶ U) a b, P V g a → P V g b → a = b) :
    ∃ a : Sec F U, ∀ (V : Scheme.{0}) (g : V ⟶ U) b, P V g b → Sec.res g a = b := by
  unfold Loc at hex
  obtain ⟨S, hS, hP⟩ := hex
  choose s hs using hP
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.EtC.sec_ext_glue R F U).2 S hS s
    (fun V W g k hg => huniq W (k ≫ g) _ _ (hres V W g k _ (hs V g hg)) (hs W (k ≫ g) _))
  refine ⟨a, fun V g b hb => _root_.GlobalTheory.EtC.ClsSpec.sep ?_⟩
  unfold Loc
  refine ⟨S.pullback g, (Scheme.etaleTopology).pullback_stable g hS, fun W k hk => ?_⟩
  show Sec.res k (Sec.res g a) = Sec.res k b
  rw [← _root_.GlobalTheory.TwSec.res_comp, ha W (k ≫ g) hk]
  exact huniq W (k ≫ g) _ _ (hs W (k ≫ g) hk) (hres V W g k b hb)

end Res

private abbrev II (q : ℕ) : Cx (ZMod q) := res (ZMod q) (tw q 1)

private abbrev dd (q : ℕ) {U : Scheme.{0}} (a : Sec ((II q).X 0) U) : Sec ((II q).X 1) U := Sec.map ((II q).d 0 1) a

private abbrev ur {V U : Scheme.{0}} (g : V ⟶ U) : (Γ(U, ⊤))ˣ →* (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom

private theorem ur_id {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : ur (𝟙 U) u = u := by
  ext; simp

private theorem ur_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    ur (k ≫ g) u = ur k (ur g u) := by
  ext
  simp [ur]
  rfl

variable {q : ℕ} [NeZero q]

private theorem unit_res {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hq.map g.appTop.hom

private theorem K_nat {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (v : (Γ(U, ⊤))ˣ) :
    Sec.res g (kumT q U v) = kumT q V (ur g v) := (_root_.GlobalTheory.EtC.KummerSplit.isKum_kumT q).1 V U g v hq

private theorem K_pow {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (Z : (Γ(U, ⊤))ˣ) (hZ : (Z : Γ(U, ⊤)) = ζ.1) (n : ℕ)
    (v : (Γ(U, ⊤))ˣ) : kumT q U (Z ^ n * v) = kumT q U v + n • resGen 1 ζ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (_root_.GlobalTheory.EtC.KummerSplit.isKum_kumT q).2 U ζ (Z ^ n * v) (Z ^ (n + 1) * v) (by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, hZ]
      ring)
    rw [h, ih, succ_nsmul, add_assoc]

private theorem tau_loc {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) (hu : u ^ q = 1) :
    Loc U fun V g => ∃ τ : Sec ((II q).X 0) V, dd q τ = 0 ∧ ∀ v, kumT q V (ur g u * v) = kumT q V v + τ := by
  refine ClsSpec.loc_trans (ClsSpec.loc_mono
    ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq) fun V g hζ => ?_)
  obtain ⟨ζ⟩ := hζ
  have hu' : (↑(ur g u) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hu, map_one, Units.val_one]
  refine _root_.GlobalTheory.TwSec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ _ hu') fun W k ha => ?_
  obtain ⟨a, ha⟩ := ha
  have hz : (Prim.map k.appTop.hom ζ).1 ^ q = 1 := _root_.GlobalTheory.EtC.PrimBasic.prim_pow_q _
  have hZ : ur (k ≫ g) u = Units.ofPowEqOne _ q hz (NeZero.ne q) ^ a := by
    ext
    rw [ur_comp, Units.val_pow_eq_pow_val, Units.val_ofPowEqOne]
    exact ha
  refine ⟨a • resGen 1 (Prim.map k.appTop.hom ζ), ?_, fun v => ?_⟩
  · have hr : Sec.map ((II q).d 0 1) (resGen 1 (Prim.map k.appTop.hom ζ)) = 0 :=
      ((_root_.GlobalTheory.EtC.resSec (ZMod q) (tw q 1) W).1 _).mpr ⟨_, rfl⟩
    show Sec.map ((II q).d 0 1) (a • resGen 1 (Prim.map k.appTop.hom ζ)) = 0
    rw [_root_.GlobalTheory.EtC.ClsSpec.smap_nsmul, hr, smul_zero]
  · rw [hZ]
    exact K_pow _ _ (Units.val_ofPowEqOne _ _ _ _) a v

private theorem kumT_ur_comp_mul_eq_add_res {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) (hu : u ^ q = 1)
    {V : Scheme.{0}} (g : V ⟶ U) (τ : Sec ((II q).X 0) V) (hτ : ∀ v, kumT q V (ur g u * v) = kumT q V v + τ)
    {W : Scheme.{0}} (k : W ⟶ V) (v : (Γ(W, ⊤))ˣ) :
    kumT q W (ur (k ≫ g) u * v) = kumT q W v + Sec.res k τ := by
  have hV := unit_res g hq
  have hW := unit_res (k ≫ g) hq
  have hu' : ur (k ≫ g) u ^ q = 1 := by rw [← map_pow, hu, map_one]
  apply _root_.GlobalTheory.EtC.ClsSpec.sep
  refine _root_.GlobalTheory.TwSec.loc_mono (tau_loc hW _ hu') fun W' k' hP => ?_
  obtain ⟨τ', _, h'⟩ := hP
  show Sec.res k' _ = Sec.res k' _
  have e1 : kumT q W' (ur k' (ur k (ur g u))) = kumT q W' 1 + τ' := by
    have := h' 1
    simpa only [ur_comp, mul_one] using this
  have e2 : kumT q W' (ur k' (ur k (ur g u))) = kumT q W' 1 + Sec.res (k' ≫ k) τ := by
    have := congrArg (Sec.res (k' ≫ k)) (hτ 1)
    rw [mul_one, K_nat _ hV, _root_.GlobalTheory.TwSec.res_add, K_nat _ hV, map_one, ur_comp] at this
    exact this
  have e3 : τ' = Sec.res (k' ≫ k) τ := add_left_cancel (e1.symm.trans e2)
  rw [K_nat _ hW, _root_.GlobalTheory.TwSec.res_add, K_nat _ hW, map_mul, ← _root_.GlobalTheory.TwSec.res_comp, ← e3]
  have := h' (ur k' v)
  simp only [ur_comp] at this ⊢
  exact this

private theorem tau_exists {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) (hu : u ^ q = 1) :
    ∃ τ : Sec ((II q).X 0) U, dd q τ = 0 ∧ ∀ v, kumT q U (u * v) = kumT q U v + τ := by
  obtain ⟨a, ha⟩ := glue (F := (II q).X 0)
    (fun V g τ => dd q τ = 0 ∧ ∀ v, kumT q V (ur g u * v) = kumT q V v + τ)
    (tau_loc hq u hu)
    (fun V W g k τ hP => ⟨by
        show Sec.map _ (Sec.res k τ) = 0
        rw [_root_.GlobalTheory.EtC.exactIff_map_res]
        exact (congrArg (Sec.res k) hP.1).trans (_root_.GlobalTheory.TwSec.res_zero k), kumT_ur_comp_mul_eq_add_res hq u hu g τ hP.2 k⟩)
    (fun V g a b ha hb => add_left_cancel ((ha.2 1).symm.trans (hb.2 1)))
  have hloc := tau_loc hq u hu
  refine ⟨a, _root_.GlobalTheory.EtC.ClsSpec.sep ?_, fun v => _root_.GlobalTheory.EtC.ClsSpec.sep ?_⟩
  · refine _root_.GlobalTheory.TwSec.loc_mono hloc fun V g hP => ?_
    show Sec.res g (Sec.map _ a) = Sec.res g 0
    rw [← _root_.GlobalTheory.EtC.exactIff_map_res, ha V g _ hP.choose_spec, _root_.GlobalTheory.TwSec.res_zero]
    exact hP.choose_spec.1
  · refine _root_.GlobalTheory.TwSec.loc_mono hloc fun V g hP => ?_
    show Sec.res g _ = Sec.res g _
    rw [K_nat g hq, map_mul, hP.choose_spec.2, _root_.GlobalTheory.TwSec.res_add, K_nat g hq, ha V g _ hP.choose_spec]

private theorem root_ratio {A : Type} [CommGroup A] {a a' : A} (h : a ^ q = a' ^ q) : (a' * a⁻¹) ^ q = 1 := by
  rw [mul_pow, inv_pow, ← h, mul_inv_cancel]

private theorem dK_eq {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) {a a' : (Γ(U, ⊤))ˣ} (h : a ^ q = a' ^ q) :
    dd q (kumT q U a) = dd q (kumT q U a') := by
  obtain ⟨τ, hτ0, hτ⟩ := tau_exists hq (a' * a⁻¹) (root_ratio h)
  have h0 : Sec.map ((II q).d 0 1) τ = 0 := hτ0
  have hA : kumT q U a' = kumT q U a + τ := by rw [← hτ a, inv_mul_cancel_right]
  show Sec.map ((II q).d 0 1) (kumT q U a) = Sec.map ((II q).d 0 1) (kumT q U a')
  rw [hA, _root_.GlobalTheory.EtC.ClsSpec.smap_add, h0, add_zero]

private abbrev ff (q : ℕ) {U : Scheme.{0}} (a b : (Γ(U, ⊤))ˣ) : Sec ((II q).X 0) U :=
  kumT q U a + kumT q U b - kumT q U (a * b)

private theorem ff_eq {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) {a a' b b' : (Γ(U, ⊤))ˣ} (ha : a ^ q = a' ^ q)
    (hb : b ^ q = b' ^ q) : ff q a b = ff q a' b' := by
  obtain ⟨τ, -, hτ⟩ := tau_exists hq (a' * a⁻¹) (root_ratio ha)
  obtain ⟨σ, -, hσ⟩ := tau_exists hq (b' * b⁻¹) (root_ratio hb)
  have e : a' * b' = a' * a⁻¹ * (b' * b⁻¹ * (a * b)) := by
    rw [show a' * a⁻¹ * (b' * b⁻¹ * (a * b)) = a' * b' * (a⁻¹ * a) * (b⁻¹ * b) by ac_rfl,
      inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]
  have hA : kumT q U a' = kumT q U a + τ := by rw [← hτ a, inv_mul_cancel_right]
  have hB : kumT q U b' = kumT q U b + σ := by rw [← hσ b, inv_mul_cancel_right]
  have hAB : kumT q U (a' * b') = kumT q U (a * b) + σ + τ := by rw [e, hτ, hσ]
  show kumT q U a + kumT q U b - kumT q U (a * b) = kumT q U a' + kumT q U b' - kumT q U (a' * b')
  rw [hA, hB, hAB]
  abel

private theorem ff_nat {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (a b : (Γ(U, ⊤))ˣ) :
    Sec.res g (ff q a b) = ff q (ur g a) (ur g b) := by
  show Sec.res g (kumT q U a + kumT q U b - kumT q U (a * b)) =
    kumT q V (ur g a) + kumT q V (ur g b) - kumT q V (ur g a * ur g b)
  rw [_root_.GlobalTheory.EtC.KummerSplit.res_sub, _root_.GlobalTheory.TwSec.res_add, K_nat g hq, K_nat g hq, K_nat g hq, map_mul]

private theorem roots {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ a : (Γ(V, ⊤))ˣ, a ^ q = ur g s := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 hq s

private theorem roots2 {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s t : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ a b : (Γ(V, ⊤))ˣ, a ^ q = ur g s ∧ b ^ q = ur g t :=
  ClsSpec.loc_mono (ClsSpec.loc_and (roots hq s) (roots hq t))
    fun _ _ ⟨⟨a, ha⟩, b, hb⟩ => ⟨a, b, ha, hb⟩

private theorem roots3 {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s t r : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ a b c : (Γ(V, ⊤))ˣ, a ^ q = ur g s ∧ b ^ q = ur g t ∧ c ^ q = ur g r :=
  ClsSpec.loc_mono (ClsSpec.loc_and (roots2 hq s t) (roots hq r))
    fun _ _ ⟨⟨a, b, ha, hb⟩, c, hc⟩ => ⟨a, b, c, ha, hb, hc⟩

private def Dd (q : ℕ) [NeZero q] {U : Scheme.{0}} (s : (Γ(U, ⊤))ˣ) : Sec ((II q).X 1) U :=
  pick fun D => ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = ur g s → Sec.res g D = dd q (kumT q V v)

private theorem Dd_spec {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s : (Γ(U, ⊤))ˣ) (V : Scheme.{0}) (g : V ⟶ U)
    (v : (Γ(V, ⊤))ˣ) (hv : v ^ q = ur g s) : Sec.res g (Dd q s) = dd q (kumT q V v) := by
  have hP : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = ur g s →
      ∀ (W : Scheme.{0}) (k : W ⟶ V) (w : (Γ(W, ⊤))ˣ), w ^ q = ur (k ≫ g) s →
        Sec.res k (dd q (kumT q V v)) = dd q (kumT q W w) := by
    intro V g v hv W k w hw
    show Sec.res k (Sec.map _ _) = _
    rw [← _root_.GlobalTheory.EtC.exactIff_map_res, K_nat k (unit_res g hq)]
    exact dK_eq (unit_res (k ≫ g) hq) (by rw [← map_pow, hv, hw, ur_comp])
  obtain ⟨D, hD⟩ := glue (F := (II q).X 1)
    (fun V g D => ∀ (W : Scheme.{0}) (k : W ⟶ V) (w : (Γ(W, ⊤))ˣ), w ^ q = ur (k ≫ g) s →
      Sec.res k D = dd q (kumT q W w))
    (_root_.GlobalTheory.TwSec.loc_mono (roots hq s) fun V g ⟨v, hv⟩ => ⟨_, hP V g v hv⟩)
    (fun V W g k D hD W' k' w hw => by
      rw [← _root_.GlobalTheory.TwSec.res_comp]
      exact hD W' (k' ≫ k) w (by rw [hw, Category.assoc]))
    (fun V g D D' hD hD' => _root_.GlobalTheory.EtC.ClsSpec.sep (_root_.GlobalTheory.TwSec.loc_mono (roots (unit_res g hq) (ur g s)) fun W k ⟨w, hw⟩ =>
      (hD W k w (by rw [hw, ur_comp])).trans (hD' W k w (by rw [hw, ur_comp])).symm))
  have hex : ∃ D, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = ur g s →
      Sec.res g D = dd q (kumT q V v) :=
    ⟨D, fun V g v hv => hD V g _ (hP V g v hv)⟩
  exact (pick_spec hex) V g v hv

private theorem Dd_root {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) {s v : (Γ(U, ⊤))ˣ} (hv : v ^ q = s) :
    Dd q s = dd q (kumT q U v) := by
  have := Dd_spec hq s U (𝟙 U) v (by rw [hv, ur_id])
  rwa [_root_.GlobalTheory.EtC.ClsSpec.res_id] at this

private theorem Dd_nat {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (s : (Γ(U, ⊤))ˣ) :
    Sec.res g (Dd q s) = Dd q (ur g s) := by
  apply _root_.GlobalTheory.EtC.ClsSpec.sep
  refine _root_.GlobalTheory.TwSec.loc_mono (roots (unit_res g hq) (ur g s)) fun W k hw => ?_
  obtain ⟨w, hw⟩ := hw
  show Sec.res k (Sec.res g (Dd q s)) = Sec.res k (Dd q (ur g s))
  rw [← _root_.GlobalTheory.TwSec.res_comp, Dd_spec hq s W (k ≫ g) w (by rw [hw, ur_comp]), Dd_spec (unit_res g hq) (ur g s) W k w hw]

private theorem Dd_closed {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s : (Γ(U, ⊤))ˣ) :
    Sec.map ((II q).d 1 2) (Dd q s) = 0 := by
  apply _root_.GlobalTheory.EtC.ClsSpec.sep
  refine _root_.GlobalTheory.TwSec.loc_mono (roots hq s) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  show Sec.res g (Sec.map _ (Dd q s)) = Sec.res g 0
  rw [← _root_.GlobalTheory.EtC.exactIff_map_res, _root_.GlobalTheory.TwSec.res_zero, Dd_spec hq s V g v hv]
  exact ClsSpec.d_d (II q) 0 1 2 _

private def Ph (q : ℕ) [NeZero q] {U : Scheme.{0}} (s t : (Γ(U, ⊤))ˣ) : Sec ((II q).X 0) U :=
  pick fun D => ∀ (V : Scheme.{0}) (g : V ⟶ U) (a b : (Γ(V, ⊤))ˣ), a ^ q = ur g s → b ^ q = ur g t →
    Sec.res g D = ff q a b

private theorem Ph_spec {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s t : (Γ(U, ⊤))ˣ) (V : Scheme.{0}) (g : V ⟶ U)
    (a b : (Γ(V, ⊤))ˣ) (ha : a ^ q = ur g s) (hb : b ^ q = ur g t) : Sec.res g (Ph q s t) = ff q a b := by
  have hP : ∀ (V : Scheme.{0}) (g : V ⟶ U) (a b : (Γ(V, ⊤))ˣ), a ^ q = ur g s → b ^ q = ur g t →
      ∀ (W : Scheme.{0}) (k : W ⟶ V) (a' b' : (Γ(W, ⊤))ˣ), a' ^ q = ur (k ≫ g) s → b' ^ q = ur (k ≫ g) t →
        Sec.res k (ff q a b) = ff q a' b' := by
    intro V g a b ha hb W k a' b' ha' hb'
    rw [ff_nat k (unit_res g hq)]
    exact ff_eq (unit_res (k ≫ g) hq) (by rw [← map_pow, ha, ha', ur_comp]) (by rw [← map_pow, hb, hb', ur_comp])
  obtain ⟨D, hD⟩ := glue (F := (II q).X 0)
    (fun V g D => ∀ (W : Scheme.{0}) (k : W ⟶ V) (a' b' : (Γ(W, ⊤))ˣ), a' ^ q = ur (k ≫ g) s →
      b' ^ q = ur (k ≫ g) t → Sec.res k D = ff q a' b')
    (_root_.GlobalTheory.TwSec.loc_mono (roots2 hq s t) fun V g ⟨a, b, ha, hb⟩ => ⟨_, hP V g a b ha hb⟩)
    (fun V W g k D hD W' k' a' b' ha' hb' => by
      rw [← _root_.GlobalTheory.TwSec.res_comp]
      exact hD W' (k' ≫ k) a' b' (by rw [ha', Category.assoc]) (by rw [hb', Category.assoc]))
    (fun V g D D' hD hD' => _root_.GlobalTheory.EtC.ClsSpec.sep (_root_.GlobalTheory.TwSec.loc_mono (roots2 (unit_res g hq) (ur g s) (ur g t)) fun W k ⟨a', b', ha', hb'⟩ =>
      (hD W k a' b' (by rw [ha', ur_comp]) (by rw [hb', ur_comp])).trans
        (hD' W k a' b' (by rw [ha', ur_comp]) (by rw [hb', ur_comp])).symm))
  have hex : ∃ D, ∀ (V : Scheme.{0}) (g : V ⟶ U) (a b : (Γ(V, ⊤))ˣ), a ^ q = ur g s → b ^ q = ur g t →
      Sec.res g D = ff q a b :=
    ⟨D, fun V g a b ha hb => hD V g _ (hP V g a b ha hb)⟩
  exact (pick_spec hex) V g a b ha hb

private theorem Ph_root {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) {s t a b : (Γ(U, ⊤))ˣ} (ha : a ^ q = s)
    (hb : b ^ q = t) : Ph q s t = ff q a b := by
  have := Ph_spec hq s t U (𝟙 U) a b (by rw [ha, ur_id]) (by rw [hb, ur_id])
  rwa [_root_.GlobalTheory.EtC.ClsSpec.res_id] at this

private theorem Ph_nat {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (s t : (Γ(U, ⊤))ˣ) :
    Sec.res g (Ph q s t) = Ph q (ur g s) (ur g t) := by
  apply _root_.GlobalTheory.EtC.ClsSpec.sep
  refine _root_.GlobalTheory.TwSec.loc_mono (roots2 (unit_res g hq) (ur g s) (ur g t)) fun W k hw => ?_
  obtain ⟨a, b, ha, hb⟩ := hw
  show Sec.res k (Sec.res g (Ph q s t)) = Sec.res k (Ph q (ur g s) (ur g t))
  rw [← _root_.GlobalTheory.TwSec.res_comp, Ph_spec hq s t W (k ≫ g) a b (by rw [ha, ur_comp]) (by rw [hb, ur_comp]),
    Ph_spec (unit_res g hq) (ur g s) (ur g t) W k a b ha hb]

section Main
variable {X : Spc}

private def fam (A0 : ∀ U : Scheme.{0}, Sx X 0 U → Sec ((II q).X 1) U) (A1 : ∀ U : Scheme.{0}, Sx X 1 U → Sec ((II q).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx X p U → Sec ((II q).X s) U
  | 0, s, h, U, x => Eq.rec (motive := fun s _ => Sec ((II q).X s) U) (A0 U x) (show (1 : ℤ) = s by simpa using h)
  | 1, s, h, U, x => Eq.rec (motive := fun s _ => Sec ((II q).X s) U) (A1 U x) (show (0 : ℤ) = s by simpa using h)
  | _ + 2, _, _, _, _ => 0

private theorem fam_nat (A0 : ∀ U : Scheme.{0}, Sx X 0 U → Sec ((II q).X 1) U)
    (A1 : ∀ U : Scheme.{0}, Sx X 1 U → Sec ((II q).X 0) U)
    (h0 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X 0 U), Sec.res g (A0 U x) = A0 V (x.res g))
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X 1 U), Sec.res g (A1 U x) = A1 V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X p U) :
    Sec.res g (fam A0 A1 p s h U x) = fam A0 A1 p s h V (x.res g) := by
  rcases p with _ | _ | p
  · obtain rfl : s = 1 := by omega
    exact h0 V U g x
  · obtain rfl : s = 0 := by omega
    exact h1 V U g x
  · exact _root_.GlobalTheory.TwSec.res_zero g

private theorem res_neg' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (-a) = - Sec.res g a := map_neg (F.obj.map g.op).hom a

private theorem main (L : X ⟶ ofCat (glCat 1)) (w : ∀ T : Scheme.{0}, Sx X 0 T → (Γ(T, ⊤))ˣ) (hI : Inv q X)
    (hT : IsTrivBy L w) : c1 q L = 0 := by
  obtain ⟨hwn, hwc⟩ := hT
  obtain ⟨γ, hγ, h0, h1, h2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hI
  rw [← hγ, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ 1 (by norm_num)]
  let A0 : ∀ U : Scheme.{0}, Sx X 0 U → Sec ((II q).X 1) U := fun U x => -Dd q (w U x)
  let A1 : ∀ U : Scheme.{0}, Sx X 1 U → Sec ((II q).X 0) U := fun U x => Ph q (lineUnit L x) (w U (x.face 0))
  have hA0 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X 0 U), Sec.res g (A0 U x) = A0 V (x.res g) := by
    intro V U g x
    show Sec.res g (-Dd q (w U x)) = -Dd q (w V (x.res g))
    rw [res_neg', Dd_nat g (hI U ⟨x⟩), hwn]
  have hA1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X 1 U), Sec.res g (A1 U x) = A1 V (x.res g) := by
    intro V U g x
    show Sec.res g (Ph q (lineUnit L x) (w U (x.face 0))) = Ph q (lineUnit L (x.res g)) (w V ((x.res g).face 0))
    rw [Ph_nat g (hI U ⟨x.face 0⟩), ClsSpec.lineUnit_res, ← ClsSpec.face_res, hwn]
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (I := II q) (n := 1) (fam A0 A1) (fam_nat A0 A1 hA0 hA1)
  have hf0 : ∀ (U : Scheme.{0}) (x : Sx X 0 U) (h : -((0 : ℕ) : ℤ) + 1 = 1), fam A0 A1 0 1 h U x = A0 U x :=
    fun _ _ _ => rfl
  have hf1 : ∀ (U : Scheme.{0}) (x : Sx X 1 U) (h : -((1 : ℕ) : ℤ) + 1 = 0), fam A0 A1 1 0 h U x = A1 U x :=
    fun _ _ _ => rfl
  have hf2 : ∀ (U : Scheme.{0}) (x : Sx X 2 U) (h : -((2 : ℕ) : ℤ) + 1 = -1), fam A0 A1 2 (-1) h U x = 0 :=
    fun _ _ _ => rfl
  have hnat := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q) (E := X) (I := II q) (n := 2)).2.1
  have hd := GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (I := II q) (show (1 : ℤ) + 1 = 2 by norm_num) β
  have hsign : (2 : ℤ).negOnePow = 1 := by decide
  refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q) (E := X) (I := II q) (n := 2)).2.2.1 _ _ fun p s h U x => ?_⟩
  rcases p with _ | _ | _ | p
  · obtain rfl : s = 2 := by omega
    rw [(hd U).1 x, h0 U x, hβ, hf0]
    show Sec.map _ (-Dd q (w U x)) = 0
    rw [smap_neg, Dd_closed (hI U ⟨x⟩), neg_zero]
  · obtain rfl : s = 1 := by omega
    have hU := hI U ⟨x.face 0⟩
    apply _root_.GlobalTheory.EtC.ClsSpec.sep
    refine _root_.GlobalTheory.TwSec.loc_mono (roots2 hU (lineUnit L x) (w U (x.face 0))) fun V g hr => ?_
    obtain ⟨v, a, hv, ha⟩ := hr
    show Sec.res g _ = Sec.res g _
    rw [hnat, hnat]
    have hV := unit_res g hU
    have hv' : v ^ q = lineUnit L (x.res g) := by rw [ClsSpec.lineUnit_res, hv]
    have ha' : a ^ q = w V ((x.res g).face 0) := by rw [← ClsSpec.face_res, hwn, ha]
    have hb' : (v * a) ^ q = w V ((x.res g).face 1) := by rw [← hwc, mul_pow, hv', ha']
    rw [(hd V).2 0 0 1 (by omega) (by omega) (x.res g), h1 V (x.res g) v hv', hsign, one_smul, Fin.sum_univ_two]
    simp only [hβ, hf0, hf1, A0, A1, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
    rw [Ph_root hV hv' ha', Dd_root hV ha', Dd_root hV hb']
    simp only [ff, _root_.GlobalTheory.EtC.ClsSpec.smap_add, _root_.GlobalTheory.EtC.KummerSplit.smap_sub]
    abel
  · obtain rfl : s = 0 := by omega
    have hU := hI U ⟨(x.face 0).face 0⟩
    apply _root_.GlobalTheory.EtC.ClsSpec.sep
    refine _root_.GlobalTheory.TwSec.loc_mono (roots3 hU (lineUnit L (x.face 2)) (lineUnit L (x.face 0)) (w U ((x.face 0).face 0)))
      fun V g hr => ?_
    obtain ⟨α, b, c, hα, hb, hc⟩ := hr
    show Sec.res g _ = Sec.res g _
    rw [hnat, hnat]
    have hV := unit_res g hU
    have hα' : α ^ q = lineUnit L ((x.res g).face 2) := by
      rw [← ClsSpec.face_res, ClsSpec.lineUnit_res, hα]
    have hb' : b ^ q = lineUnit L ((x.res g).face 0) := by
      rw [← ClsSpec.face_res, ClsSpec.lineUnit_res, hb]
    have hc' : c ^ q = w V (((x.res g).face 0).face 0) := by
      rw [← ClsSpec.face_res, ← ClsSpec.face_res, hwn, hc]
    have e1 : ((x.res g).face 1).face 0 = ((x.res g).face 0).face 0 :=
      ClsSpec.face_face _ 1 0 0 0 (by ext i; fin_cases i; rfl)
    have e2 : ((x.res g).face 2).face 0 = ((x.res g).face 0).face 1 :=
      ClsSpec.face_face _ 2 0 0 1 (by ext i; fin_cases i; rfl)
    have hαb : (α * b) ^ q = lineUnit L ((x.res g).face 1) := by rw [_root_.GlobalTheory.EtC.ClsSpec.lineUnit_face, mul_pow, hα', hb']
    have hbc : (b * c) ^ q = w V (((x.res g).face 2).face 0) := by rw [e2, ← hwc, mul_pow, hb', hc']
    have hc1 : c ^ q = w V (((x.res g).face 1).face 0) := by rw [e1, hc']
    have hz : ∀ (φ : (II q).X (-1) ⟶ (II q).X 0), Sec.map φ (0 : Sec _ V) = 0 :=
      fun φ => map_zero (φ.hom.app (op V)).hom
    rw [(hd V).2 1 (-1) 0 (by omega) (by omega) (x.res g),
      h2 V (x.res g) α b (by rw [ClsSpec.sub_zero_one, hα'])
      (by rw [ClsSpec.sub_one_one, hb']), hsign, one_smul, Fin.sum_univ_three]
    simp only [hβ, hf1, hf2, hz, A1, zero_add, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      neg_one_sq, one_smul, neg_smul]
    rw [Ph_root hV hb' hc', Ph_root hV hαb hc1, Ph_root hV hα' hbc]
    simp only [ff, mul_assoc]
    abel
  · exact @Subsingleton.elim _ ((_root_.GlobalTheory.EtC.resSec (ZMod q) (tw q 1) U).2.2.2 s (by omega)) _ _

end Main

end UpperTheory.ChernClassOfTrivializedBundle

end

theorem UpperTheory.firstChernClass_eq_zero_of_isTrivialized :
    ∀ (q : ℕ) [NeZero q] {X : Spc} (L : X ⟶ ofCat (glCat 1)) (w : ∀ T : Scheme.{0}, Sx X 0 T → (Γ(T, ⊤))ˣ), Inv q X → IsTrivBy L w → c1 q L = 0 := by
  intro q _ X L w hI hT
  exact UpperTheory.ChernClassOfTrivializedBundle.main L w hI hT
