module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalLocDerOfIsCob
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstKOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfIdModEpsThickening
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof
import Mathlib.Tactic.Linter.Style

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.KS GlobalTheory.KS.GlueDer GlobalTheory.LogKS

namespace GlobalTheory.InteriorKS

theorem glue_along {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (D : R → K) {I : Type} (W : I → X.Opens) (hW : ∀ y, ∃ i, m y ∈ W i)
    (e : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)) (he : ∀ i, LocDerK q p m D (W i) (e i))
    (hc : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, e i O f = e j O f) :
    ∃ d₁, LocDerK q p m D ⊤ d₁ ∧ ∀ (O : X.Opens) (f : Γ(X, O)) (s : Γ(Y, m ⁻¹ᵁ O)),
      (∀ i, resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = e i (O ⊓ W i) (resG X inf_le_left f)) → d₁ O f = s := by
  have cov : ∀ O : X.Opens, m ⁻¹ᵁ O ≤ ⨆ i, m ⁻¹ᵁ (O ⊓ W i) := fun O y hy =>
    let ⟨i, hi⟩ := hW y; TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hy, hi⟩
  have ex : ∀ (O : X.Opens) (f : Γ(X, O)), ∃ s : Γ(Y, m ⁻¹ᵁ O), ∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = e i (O ⊓ W i) (resG X inf_le_left f) := fun O f =>
    (Y.sheaf.existsUnique_gluing' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (cov O)
      (fun i => e i (O ⊓ W i) (resG X inf_le_left f)) fun i j => by
        have hi := (he i).res (O ⊓ W i) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_left inf_le_right (resG X inf_le_left f)
        have hj := (he j).res (O ⊓ W j) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_right inf_le_right (resG X inf_le_left f)
        rw [rsT_eq (pre_mono m inf_le_left), res_res] at hi
        rw [rsT_eq (pre_mono m inf_le_right), res_res] at hj
        exact hi.symm.trans ((hc i j _ (inf_le_inf inf_le_right inf_le_right) _).trans hj)).imp
      fun _ hs => hs.1
  have ext : ∀ (O : X.Opens) (s t : Γ(Y, m ⁻¹ᵁ O)), (∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) t) →
      s = t := fun O =>
    Y.sheaf.eq_of_locally_eq' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O) (fun i => homOfLE (pre_mono m inf_le_left)) (cov O)
  choose d₁ hd using ex
  refine ⟨d₁, ⟨fun O _ f f' => ext O _ _ fun i => by
      rw [map_add (f := _), hd, hd, hd, map_add (f := _), (he i).add _ inf_le_right],
    fun O _ f f' => ext O _ _ fun i => by
      rw [map_add (f := _), map_mul, map_mul, hd, hd, hd, map_mul, (he i).mul _ inf_le_right,
        res_app m inf_le_left, res_app m inf_le_left],
    fun O O' h _ f => ext O' _ _ fun i => by
      have h' : O' ⊓ W i ≤ O ⊓ W i := inf_le_inf_right _ h
      have h1 := (he i).res (O ⊓ W i) (O' ⊓ W i) h' inf_le_right (resG X inf_le_left f)
      rw [rsT_eq (pre_mono m h'), res_res, ← hd, res_res] at h1
      rw [hd, rsT_eq (pre_mono m h), res_res, res_res, h1],
    fun O _ r => ext O _ _ fun i => by rw [hd, res_const, res_const, (he i).base _ inf_le_right]⟩,
    fun O f s hs => ext O _ _ fun i => (hd O f i).trans (hs i).symm⟩

theorem chart_appLE {X : Scheme.{0}} (U : X.affineOpens) (h : ⊤ ≤ chart U ⁻¹ᵁ U.1) :
    (chart U).appLE U.1 ⊤ h = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
  show U.2.fromSpec.app U.1 ≫ (Spec Γ(X, U.1)).presheaf.map (homOfLE h).op = _
  rw [U.2.fromSpec_app_self, Category.assoc]
  erw [← Functor.map_comp]
  exact (congrArg (_ ≫ ·) ((Spec Γ(X, U.1)).presheaf.map_id _)).trans (Category.comp_id _)

theorem top_le_chart {X : Scheme.{0}} (U : X.affineOpens) : ⊤ ≤ chart U ⁻¹ᵁ U.1 :=
  U.2.fromSpec_preimage_self.ge

theorem appLE_eq_constFn {X Y : Scheme.{0}} (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (q : Y ⟶ Sp S) (a : Y ⟶ X) (ha : a = q ≫ spMap φ ≫ chart U) (W : Y.Opens) (h : W ≤ a ⁻¹ᵁ U.1) (r : Γ(X, U.1)) :
    (a.appLE U.1 W h).hom r = constFn q W (φ r) := by
  subst ha
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ r) =
      ((spMap φ).appTop).hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom r) :=
    congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have e : (q ≫ spMap φ ≫ chart U).appLE U.1 W h =
      (chart U).appLE U.1 ⊤ (top_le_chart U) ≫ (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) ≫
        q.appLE ⊤ W (fun _ _ => trivial) := by
    erw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]; simp only [Category.assoc]
  rw [e, chart_appLE, constFn, h2, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem ext_affineOpen {X Y : Scheme.{0}} (U : X.affineOpens) (a b : Y ⟶ X) (ha : ⊤ ≤ a ⁻¹ᵁ U.1) (hb : ⊤ ≤ b ⁻¹ᵁ U.1)
    (h : a.appLE U.1 ⊤ ha = b.appLE U.1 ⊤ hb) : a = b := by
  have key : ∀ (a : Y ⟶ X) (ha : ⊤ ≤ a ⁻¹ᵁ U.1),
      a = Y.toSpecΓ ≫ Spec.map (a.appLE U.1 ⊤ ha) ≫ U.2.fromSpec := fun a ha => by
    have := IsAffineOpen.isOpenImmersion_fromSpec (show IsAffineOpen U.1 from U.2)
    obtain ⟨a', rfl⟩ : ∃ a', a' ≫ U.2.fromSpec = a :=
      ⟨_, IsOpenImmersion.lift_fac _ _ (by rw [U.2.range_fromSpec]; rintro _ ⟨y, rfl⟩; exact ha (Set.mem_univ y))⟩
    have e : (a' ≫ U.2.fromSpec).appLE U.1 ⊤ ha = (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ a'.appTop := by
      rw [← chart_appLE U (top_le_chart U), Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Spec.map_comp, ← Category.assoc, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc a',
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key a ha, key b hb, h]

theorem app_eq_zero_of_valR {Y Z : Scheme.{0}} (m : Y ⟶ Z) (O : Z.Opens) (f : Γ(Z, O))
    (h : ∀ Ω : Y.affineOpens, Ω.1 ≤ m ⁻¹ᵁ O → valR (chart Ω ≫ m) O f = 0) : (m.app O).hom f = 0 := by
  refine Y.sheaf.eq_of_locally_eq' (fun Ω : {Ω : Y.affineOpens // Ω.1 ≤ m ⁻¹ᵁ O} => Ω.1.1) (m ⁻¹ᵁ O)
    (fun Ω => homOfLE Ω.2) (fun y hy => by
      obtain ⟨Ω, hΩ, hy', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨Ω, hΩ⟩, hle⟩, hy'⟩) _ _ fun Ω => ?_
  have h0 : ⊤ ≤ (chart Ω.1 ≫ m) ⁻¹ᵁ O := fun p hp => Ω.2 (top_le_chart Ω.1 hp)
  have h1 := h Ω.1 Ω.2
  rw [valR, dite_eq_left h0, ← Scheme.Hom.appLE_comp_appLE (chart Ω.1) m O Ω.1.1 ⊤ Ω.2 (top_le_chart _), chart_appLE] at h1
  have h2 : (m.appLE O Ω.1.1 Ω.2).hom f = 0 :=
    (congrArg (fun ψ => ψ.hom ((m.appLE O Ω.1.1 Ω.2).hom f)) (Scheme.ΓSpecIso Γ(Y, Ω.1.1)).inv_hom_id).symm.trans h1
  exact h2.trans (map_zero _).symm

theorem isField_intCast {Z : Scheme.{0}} {W O : Z.Opens} {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)} (hd : IsField W d)
    (hO : O ≤ W) (r : ℤ) : d O (r : Γ(Z, O)) = 0 := by
  have h1 : d O 1 = 0 := left_eq_add.1 (by simpa using hd.2.1 O hO 1 1 : d O 1 = _)
  rw [← zsmul_one, ← AddMonoidHom.mk'_apply (d O) (hd.1 O hO), map_zsmul, AddMonoidHom.mk'_apply, h1, smul_zero]

theorem constFn_int {Z : Scheme.{0}} (p : Z ⟶ Sp ℤ) (O : Z.Opens) (r : ℤ) : constFn p O r = (r : Γ(Z, O)) :=
  eq_intCast ((p.appLE ⊤ O (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom) r

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (V : X.Opens)
  (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1))
  (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1))

theorem exists_global_lift (hv : ∀ a, IsTanAtG t (chart U) (v a)) (hKS : IsKS t V U v D Θ) {K : Type} [Field K]
    (φ₀ : Γ(X, U.1) →+* K) (hΘ : ∀ a b, φ₀ (Θ a b) = 0) (hV : ⊤ ≤ (spMap φ₀ ≫ chart U) ⁻¹ᵁ V) {Y : Scheme.{0}}
    (q : Y ⟶ Sp K) (m : Y ⟶ t.G.left) (hm : m ≫ t.G.hom = q ≫ spMap φ₀ ≫ chart U) (p : t.G.left ⟶ Sp ℤ) :
    ∃ d₁, LocDerK q p m (fun _ => 0) ⊤ d₁ ∧
      ∀ r, d₁ (t.G.hom ⁻¹ᵁ U.1) ((t.G.hom.app U.1).hom r) = constFn q _ (φ₀ (D r)) := by
  obtain ⟨J, W, j, d, hcov, -, hfield, hlift, hdiff⟩ := hKS
  have hW₀ : ∀ k, W k ≤ t.G.hom ⁻¹ᵁ U.1 := fun k p hp => (hcov ▸ le_iSup W k hp).1
  refine Exists.imp (fun d₁ h => ⟨h.1, fun r => h.2 _ _ _ fun i => ?_⟩)
    (glue_along q p m (fun _ => 0) W (fun y => TopologicalSpace.Opens.mem_iSup.1 <| hcov ▸ by
      change (m ≫ t.G.hom) y ∈ U.1 ⊓ V; rw [hm]
      exact ⟨top_le_chart U (Set.mem_univ ((q ≫ spMap φ₀) y)), hV (Set.mem_univ (q y))⟩)
      (fun i O f => (m.app O).hom (d i O f))
      (fun i => ⟨fun O hO _ _ => by rw [(hfield i).1 O hO, map_add (f := _)],
        fun O hO _ _ => by rw [(hfield i).2.1 O hO, map_add (f := _), map_mul, map_mul],
        fun O O' h hO _ => by rw [(hfield i).2.2 O O' h hO, rsT_eq (pre_mono m h), res_app m h],
        fun O hO _ => by rw [constFn_int, isField_intCast (hfield i) hO, map_zero, constFn, map_zero, map_zero]⟩)
      (fun i i' O hO f => by
        rw [← sub_eq_zero, ← map_sub]
        refine app_eq_zero_of_valR m O _ fun Ω hΩ => ?_
        obtain ⟨ψ, hψ⟩ : ∃ ψ : K →+* Γ(Y, Ω.1), spMap ψ = chart Ω ≫ q :=
          ⟨(Spec.preimage (chart Ω ≫ q)).hom, Spec.map_preimage _⟩
        have hg : (chart Ω ≫ m) ≫ t.G.hom = spMap (ψ.comp φ₀) ≫ chart U := by
          rw [Category.assoc, hm, ← Category.assoc, ← hψ, ← Category.assoc, spMap_comp']
        choose w hw using fun a => (existsUnique_isTranslate t (ψ.comp φ₀) hg (hv a)).exists
        rw [hdiff i i' O hO f _ (ψ.comp φ₀) (chart Ω ≫ m) w hg (fun p hp => hΩ (top_le_chart Ω hp)) hw]
        simp [hΘ]))
  have e1 : resG t.G.left (inf_le_left : t.G.hom ⁻¹ᵁ U.1 ⊓ W i ≤ _) ((t.G.hom.app U.1).hom r) =
      resG t.G.left (inf_le_right : t.G.hom ⁻¹ᵁ U.1 ⊓ W i ≤ _) ((t.G.hom.appLE U.1 (W i) (hW₀ i)).hom r) :=
    (congrArg (fun ψ => ψ.hom r) (Scheme.Hom.appLE_map t.G.hom (hW₀ i)
      (homOfLE (inf_le_right : t.G.hom ⁻¹ᵁ U.1 ⊓ W i ≤ _)).op)).symm
  rw [res_const, e1, (hfield i).2.2 _ _ _ le_rfl, hlift i (hW₀ i), ← res_app m _ (pre_mono m inf_le_right),
    ← res_const q (pre_mono m (inf_le_right : t.G.hom ⁻¹ᵁ U.1 ⊓ W i ≤ _))]
  congr 1
  rw [← appLE_eq_constFn U φ₀ q _ hm _ (pre_mono m (hW₀ i)), Scheme.Hom.app_eq_appLE]
  exact (congrArg (fun ψ => ψ.hom (D r)) (Scheme.Hom.appLE_comp_appLE m t.G.hom U.1 (W i) _ (hW₀ i) le_rfl)).symm

theorem exists_isConstK (hv : ∀ a, IsTanAtG t (chart U) (v a)) (hKS : IsKS t V U v D Θ) {K : Type} [Field K]
    (φ : Γ(X, U.1) →+* DualNumber K) (hφ : ∀ r, (φ r).snd = (φ (D r)).fst) (hΘ : ∀ a b, (φ (Θ a b)).fst = 0)
    (hV : ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ V) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (ι' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (hA' : IsAbelianScheme A')
    (hι' : IsGrpPullback A' t.G (spMap φ ≫ chart U) ι')
    (hi : IsGrpPullback A A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) i) : ∃ ρ, IsConstK A' A ρ i := by
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hA' hi
  let φ₀ : Γ(X, U.1) →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom.comp φ
  have hφ₀ : spMap φ₀ = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap φ := (spMap_comp' _ _).symm
  have hm : (i ≫ ι') ≫ t.G.hom = A.hom ≫ spMap φ₀ ≫ chart U := by
    rw [Category.assoc, hι'.1.w, ← Category.assoc, hi.1.w, hφ₀]
    simp only [Category.assoc]
  let p : t.G.left ⟶ Sp ℤ := specZIsTerminal.from _
  obtain ⟨d, hd, hdD⟩ := exists_global_lift t V U v D Θ hv hKS φ₀ hΘ (by
    rw [hφ₀, Category.assoc]
    exact fun z _ => hV (Set.mem_univ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom z))) A.hom (i ≫ ι') hm p
  have hfs : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; congr 1
  obtain ⟨C, ρ, π, P⟩ : ∃ (C : Scheme.{0}) (ρ : C ⟶ A.left) (π : C ⟶ Sp (DualNumber K)),
      IsPullback ρ π A.hom (spMap (algebraMap K (DualNumber K))) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  let j₀ : A.left ⟶ C := P.lift (𝟙 _) (A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
    (by rw [Category.assoc, hfs, Category.id_comp, Category.comp_id])
  have e1 : j₀ ≫ ρ = 𝟙 _ := P.lift_fst _ _ _
  have e2 : j₀ ≫ π = A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := P.lift_snd _ _ _
  obtain ⟨hO, Pj, -⟩ := GlobalTheory.ConstThickening.structure_dualNumber K _ _ A.hom π ρ j₀ P e1 e2
  obtain ⟨Φ, hΦ1, -, hΦ3⟩ := GlobalTheory.KS.DerMorK.exists_hom_of_derivation K _ _ A.hom π ρ j₀ P e1 e2 ℤ
    (Int.castRingHom (DualNumber K)) t.G.left p (i ≫ ι') d (specZIsTerminal.hom_ext _ _)
    (by convert hd using 2; simp)
  have hmU : ⊤ ≤ (i ≫ ι') ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    show ⊤ ≤ ((i ≫ ι') ≫ t.G.hom) ⁻¹ᵁ U.1; rw [hm]
    exact fun z _ => top_le_chart U (Set.mem_univ ((A.hom ≫ spMap φ₀) z))
  have hT : ⊤ ≤ ρ ⁻¹ᵁ ((i ≫ ι') ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1)) := fun z _ => hmU (Set.mem_univ (ρ z))
  have hΦU : ρ ⁻¹ᵁ ((i ≫ ι') ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1)) ≤ Φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) :=
    hΦ1 ▸ (hO (Φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1))).le
  have hΦ2 : Φ ≫ t.G.hom = π ≫ spMap φ ≫ chart U := by
    have hb : ⊤ ≤ (π ≫ spMap φ ≫ chart U) ⁻¹ᵁ U.1 := fun z _ => top_le_chart U (Set.mem_univ ((π ≫ spMap φ) z))
    refine ext_affineOpen U _ _ (hT.trans hΦU) hb ?_
    ext r
    have h3 := hΦ3 _ ((t.G.hom.app U.1).hom r)
    rw [hdD, pbT, dite_eq_left hΦU, pbT, dite_eq_left (by exact le_rfl), pbT, dite_eq_left le_rfl, ← Scheme.Hom.app_eq_appLE ρ,
      app_const _ A.hom π ρ P.w] at h3
    have h4 := congrArg (resG C hT) h3
    rw [map_add (f := _), map_mul, res_const, res_const] at h4
    have a1 : ((Φ ≫ t.G.hom).appLE U.1 ⊤ (hT.trans hΦU)).hom r =
        resG C hT ((Φ.appLE _ _ hΦU).hom ((t.G.hom.app U.1).hom r)) := by
      rw [Scheme.Hom.comp_appLE]
      exact (congrArg (fun ψ => ψ.hom ((t.G.hom.app U.1).hom r)) (Scheme.Hom.appLE_map Φ hΦU (homOfLE hT).op)).symm
    have a2 : resG C hT (((ρ ≫ i ≫ ι').appLE (t.G.hom ⁻¹ᵁ U.1) _ le_rfl).hom ((t.G.hom.app U.1).hom r)) =
        constFn π ⊤ (algebraMap K (DualNumber K) (φ₀ r)) := by
      rw [← RingHom.comp_apply (algebraMap K _), ← appLE_eq_constFn U _ π ((ρ ≫ i ≫ ι') ≫ t.G.hom) (by
        rw [Category.assoc, hm, ← Category.assoc, P.w, ← spMap_comp' φ₀ (algebraMap K (DualNumber K))]
        simp only [Category.assoc]) ⊤ hT, Scheme.Hom.comp_appLE]
      exact congrArg (fun ψ => ψ.hom ((t.G.hom.app U.1).hom r))
        (Scheme.Hom.appLE_map (ρ ≫ i ≫ ι') le_rfl (homOfLE hT).op)
    refine (a1.trans (h4.trans ?_)).trans (appLE_eq_constFn U φ π _ rfl ⊤ hb r).symm
    refine (congrArg (· + _) a2).trans ?_
    unfold constFn; rw [← map_mul, ← map_add (f := _), ← map_mul, ← map_add (f := _)]
    congr 2; ext <;> simp [φ₀, hφ, TrivSqZeroExt.algebraMap_eq_inl]
  let e := hι'.1.lift Φ π hΦ2
  have f2 : e ≫ A'.hom = π := hι'.1.lift_snd _ _ _
  have f3 : j₀ ≫ e = i := hι'.1.hom_ext (by rw [Category.assoc, hι'.1.lift_fst, hΦ1])
    (by rw [Category.assoc, f2, e2, hi.1.w])
  have hflat : Flat π := MorphismProperty.of_isPullback (P := @Flat) P (inferInstance : Flat A.hom)
  have : IsIso e := GlobalTheory.isIso_of_id_mod_eps K _ _ _ A.hom _ A'.hom j₀ i e Pj hi.1 hflat f2 f3
  refine exists_isConstK_of_isPullback GlobalTheory.abelianSchemeLaws_all.1 K A A' (inv e ≫ ρ) i hA hA' hi ?_
    (by rw [← f3, Category.assoc, IsIso.hom_inv_id_assoc, e1])
  exact IsPullback.of_iso P (asIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simpa using f2.symm)
    (by simp) (by simp)

end GlobalTheory.InteriorKS
