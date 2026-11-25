module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.AffAcyc

section Cochains

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

theorem dn_apply (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (z : Cn F n) (c : Fin (n + 2) ⥤ C) :
    dn F n z c = ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) •
      mp F (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) (z (face i c)) := by
  simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply]; rfl

def sc (F : C ⥤ CommAlgCat.{0} R) (g : ∀ T, F.obj T) (n : ℕ) (z : Cn F n) : Cn F n :=
  fun c ↦ g (c.obj (Fin.last n)) * z c

theorem dn_sc (F : C ⥤ CommAlgCat.{0} R) (g : ∀ T, F.obj T)
    (hg : ∀ (T T' : C) (φ : T ⟶ T'), mp F φ (g T) = g T') (n : ℕ) (z : Cn F n) :
    dn F n (sc F g n z) = sc F g (n + 1) (dn F n z) := by
  funext c
  simp only [sc, dn_apply, Finset.mul_sum, mul_smul_comm]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg _ ((map_mul _ _ _).trans (congrArg (· * _) (hg _ _ _)))

end Cochains

theorem altSum {R : Type} [CommRing R] (m : ℕ) :
    2 * (∑ i : Fin m, (-1 : R) ^ (i : ℕ)) + (-1) ^ m = 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last, pow_succ]; linear_combination ih

section Pointed

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]

def G1 (a₀ : P) : Pᵒᵖ ⥤ Pᵒᵖ :=
  (show Monotone fun a : P ↦ a ⊓ a₀ from fun _ _ h ↦ inf_le_inf_right a₀ h).functor.op

def th (a₀ : P) : 𝟭 Pᵒᵖ ⟶ G1 a₀ where
  app T := (homOfLE inf_le_left : T.unop ⊓ a₀ ⟶ T.unop).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def th' (a₀ : P) : (Functor.const Pᵒᵖ).obj (op a₀) ⟶ G1 a₀ where
  app T := (homOfLE inf_le_right : T.unop ⊓ a₀ ⟶ a₀).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

variable (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (a₀ : P)
  (hb : ∀ T : Pᵒᵖ, Function.Bijective (mp F ((th a₀).app T)))

def io (T : Pᵒᵖ) : F.obj T ≃ₐ[R] F.obj ((G1 a₀).obj T) :=
  AlgEquiv.ofBijective (mp F ((th a₀).app T)) (hb T)

theorem io_nat {T T' : Pᵒᵖ} (φ : T ⟶ T') (b : F.obj ((G1 a₀).obj T)) :
    (io F a₀ hb T').symm (mp F ((G1 a₀).map φ) b) = mp F φ ((io F a₀ hb T).symm b) := by
  apply (io F a₀ hb T').injective
  have e : φ ≫ (th a₀).app T' = (th a₀).app T ≫ (G1 a₀).map φ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  change _ = mp F ((th a₀).app T') (mp F φ ((io F a₀ hb T).symm b))
  rw [AlgEquiv.apply_symm_apply, ← mp_comp, e, mp_comp]
  exact congrArg (mp F ((G1 a₀).map φ)) ((io F a₀ hb T).apply_symm_apply b).symm

def m1 : CoefMap (RingHom.id R) F F where
  G := G1 a₀
  α T := ((io F a₀ hb T).symm : _ →ₐ[R] _).toRingHom
  naturality φ b := io_nat F a₀ hb φ b
  smul T r b := map_smul (io F a₀ hb T).symm r b

def m2 : CoefMap (RingHom.id R) F F where
  G := (Functor.const Pᵒᵖ).obj (op a₀)
  α T := (((io F a₀ hb T).symm : F.obj ((G1 a₀).obj T) →ₐ[R] F.obj T).comp
    (mp F ((th' a₀).app T))).toRingHom
  naturality {T T'} φ b := by
    change (io F a₀ hb T').symm (mp F ((th' a₀).app T') (mp F (𝟙 (op a₀)) b)) =
      mp F φ ((io F a₀ hb T).symm (mp F ((th' a₀).app T) b))
    rw [← io_nat, ← mp_comp, ← mp_comp]; congr 2
  smul T r b := map_smul (((io F a₀ hb T).symm : F.obj ((G1 a₀).obj T) →ₐ[R] F.obj T).comp
    (mp F ((th' a₀).app T))) r b

def E (n : ℕ) (t : F.obj (op a₀)) : Cn F n := fun c ↦ (m2 F a₀ hb).α (c.obj (Fin.last n)) t

theorem dn_E (n : ℕ) (t : F.obj (op a₀)) (c : Fin (n + 2) ⥤ Pᵒᵖ) :
    dn F n (E F a₀ hb n t) c = (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) • E F a₀ hb (n + 1) t c := by
  rw [dn_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ ?_
  have := (m2 F a₀ hb).naturality (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) t
  refine this.symm.trans ?_
  change (m2 F a₀ hb).α _ (mp F (𝟙 (op a₀)) t) = _
  rw [mp_id]; rfl

theorem dn_const (n : ℕ) (z : Cn F n) :
    dn F n z ((Functor.const (Fin (n + 2))).obj (op a₀)) =
      (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) • z ((Functor.const (Fin (n + 1))).obj (op a₀)) := by
  rw [dn_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg _ (mp_id F (op a₀) _)

include hb in
theorem pointed (hH : HtpySt) (n : ℕ) (z : Cn F (n + 1)) (hz : dn F (n + 1) z = 0) :
    ∃ y, dn F n y = z := by
  obtain ⟨-, h1⟩ := hH R Pᵒᵖ F Pᵒᵖ F (CoefMap.id F) (m1 F a₀ hb) (th a₀)
    fun T b ↦ (io F a₀ hb T).symm_apply_apply b
  obtain ⟨-, h2⟩ := hH R Pᵒᵖ F Pᵒᵖ F (m2 F a₀ hb) (m1 F a₀ hb) (th' a₀) fun _ _ ↦ rfl
  obtain ⟨y₁, e₁⟩ := h1 n z hz
  obtain ⟨y₂, e₂⟩ := h2 n z hz
  set t : F.obj (op a₀) := z ((Functor.const (Fin (n + 2))).obj (op a₀))
  have k' : (∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ)) • t = 0 := (hz ▸ dn_const F a₀ (n + 1) z).symm
  have s : (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) + ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) = 1 := by
    have := altSum (R := R) (n + 2)
    rw [Fin.sum_univ_castSucc (n := n + 2)]
    simp only [Fin.val_castSucc, Fin.val_last] at *
    linear_combination this
  have e3 : E F a₀ hb (n + 1) t = dn F n (E F a₀ hb n t) := funext fun c ↦ by
    have h0 : (∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ)) • E F a₀ hb (n + 1) t c = 0 :=
      ((m2 F a₀ hb).smul (c.obj (Fin.last (n + 1))) _ t).symm.trans
        ((congrArg ((m2 F a₀ hb).α (c.obj (Fin.last (n + 1)))) k').trans (map_zero _))
    rw [dn_E]
    calc E F a₀ hb (n + 1) t c = (1 : R) • E F a₀ hb (n + 1) t c := (one_smul _ _).symm
      _ = ((∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ)) + ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ)) •
          E F a₀ hb (n + 1) t c := by rw [s]
      _ = _ := by rw [add_smul, h0, add_zero]
  have e0 : pulln (CoefMap.id F) (n + 1) z = z := rfl
  have e2 : pulln (m2 F a₀ hb) (n + 1) z = E F a₀ hb (n + 1) t := rfl
  refine ⟨y₁ - y₂ + E F a₀ hb n t, ?_⟩
  rw [map_add (f := _), map_sub, ← e₁, ← e₂, ← e3, e0, e2]; abel

end Pointed

section Transfer

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

theorem common_exp {J : Type} [Finite J] (p : J → ℕ → Prop) (hp : ∀ i, ∃ N, ∀ M, N ≤ M → p i M) :
    ∃ N, ∀ i, p i N := by
  choose N hN using hp
  obtain ⟨B, hB⟩ := (Set.finite_range N).bddAbove
  exact ⟨B, fun i ↦ hN i B (hB ⟨i, rfl⟩)⟩

def nat {F F' : C ⥤ CommAlgCat.{0} R} (ρ : ∀ T, F.obj T →ₐ[R] F'.obj T)
    (hρ : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), ρ T' (mp F φ b) = mp F' φ (ρ T b)) :
    CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α T := (ρ T).toRingHom
  naturality φ b := hρ φ b
  smul T r b := map_smul (ρ T) r b

theorem transfer (hC : CxSt) {F F' : C ⥤ CommAlgCat.{0} R} (ρ : ∀ T, F.obj T →ₐ[R] F'.obj T)
    (hρ : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), ρ T' (mp F φ b) = mp F' φ (ρ T b))
    (g : ∀ T, F.obj T) (hg : ∀ (T T' : C) (φ : T ⟶ T'), mp F φ (g T) = g T')
    (loc1 : ∀ T (y' : F'.obj T), ∃ (N : ℕ) (y : F.obj T), ρ T y = ρ T (g T) ^ N * y')
    (loc2 : ∀ T (y : F.obj T), ρ T y = 0 → ∃ N : ℕ, g T ^ N * y = 0)
    (n : ℕ) [Finite (Fin (n + 1) ⥤ C)] [Finite (Fin (n + 2) ⥤ C)]
    (hex : ∀ z' : Cn F' (n + 1), dn F' (n + 1) z' = 0 → ∃ y', dn F' n y' = z')
    (z : Cn F (n + 1)) (hz : dn F (n + 1) z = 0) :
    ∃ (N : ℕ) (y : Cn F n), dn F n y = sc F (fun T ↦ g T ^ N) (n + 1) z := by
  let m := nat ρ hρ
  have comm : ∀ k w, pulln m (k + 1) (dn F k w) = dn F' k (pulln m k w) := fun k w ↦
    LinearMap.congr_fun ((hC R C F).2 C F' m k) w
  obtain ⟨y', hy'⟩ := hex (pulln m (n + 1) z) (by rw [← comm, hz, map_zero])
  obtain ⟨N, hN⟩ := common_exp (J := Fin (n + 1) ⥤ C)
    (fun c N ↦ ∃ y : F.obj (c.obj (Fin.last n)), ρ _ y = ρ _ (g _) ^ N * y' c) fun c ↦ by
    obtain ⟨N, y, hy⟩ := loc1 _ (y' c)
    exact ⟨N, fun M hM ↦ ⟨g _ ^ (M - N) * y, by rw [map_mul, hy, map_pow, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hM]⟩⟩
  choose y hy using hN
  have e2 : pulln m (n + 1) (dn F n y - sc F (fun T ↦ g T ^ N) (n + 1) z) = 0 := by
    rw [map_sub, comm, show pulln m n y = sc F' (fun T ↦ ρ T (g T) ^ N) n y' from funext hy,
      dn_sc F' _ (fun T T' φ ↦ by rw [map_pow, ← hρ, hg]), hy', sub_eq_zero]
    exact funext fun c ↦ by
      change ρ _ (g (c.obj (Fin.last (n + 1)))) ^ N * ρ _ (z c) = ρ _ (g (c.obj (Fin.last (n + 1))) ^ N * z c)
      rw [map_mul, map_pow]
  obtain ⟨M, hM⟩ := common_exp (J := Fin (n + 2) ⥤ C)
    (fun c M ↦ g (c.obj (Fin.last (n + 1))) ^ M * (dn F n y - sc F (fun T ↦ g T ^ N) (n + 1) z) c = 0) fun c ↦ by
    obtain ⟨M, hM⟩ := loc2 _ _ (congrFun e2 c)
    have hM' : g (c.obj (Fin.last (n + 1))) ^ M * (dn F n y - sc F (fun T ↦ g T ^ N) (n + 1) z) c = 0 := hM
    exact ⟨M, fun K hK ↦ by rw [← Nat.sub_add_cancel hK, pow_add, _root_.mul_assoc, hM', mul_zero]⟩
  refine ⟨M + N, sc F (fun T ↦ g T ^ M) n y, ?_⟩
  rw [dn_sc F _ fun T T' φ ↦ by rw [map_pow, hg]]
  funext c
  have hMc := hM c
  rw [Pi.sub_apply, mul_sub, sub_eq_zero] at hMc
  exact hMc.trans (by change g _ ^ M * (g _ ^ N * z c) = g _ ^ (M + N) * z c; rw [pow_add, _root_.mul_assoc])

theorem exact_of_span {B : Type} [CommRing B] (F : C ⥤ CommAlgCat.{0} R) (io' : ∀ T, B →+* F.obj T)
    (hio : ∀ (T T' : C) (φ : T ⟶ T') (b : B), mp F φ (io' T b) = io' T' b) (S : Set B)
    (hS : Ideal.span S = ⊤) (n : ℕ) (z : Cn F (n + 1))
    (h : ∀ f ∈ S, ∃ (N : ℕ) (y : Cn F n), dn F n y = sc F (fun T ↦ io' T f ^ N) (n + 1) z) :
    ∃ y, dn F n y = z := by
  let I : Ideal B :=
    { carrier := {b | ∃ y, dn F n y = sc F (fun T ↦ io' T b) (n + 1) z}
      add_mem' := fun {a b} ⟨y, hy⟩ ⟨y', hy'⟩ ↦ ⟨y + y', by
        rw [map_add (f := _), hy, hy']; funext c; simp [sc, add_mul]⟩
      zero_mem' := ⟨0, by rw [map_zero]; funext c; simp [sc]⟩
      smul_mem' := fun a {b} ⟨y, hy⟩ ↦ ⟨sc F (fun T ↦ io' T a) n y, by
        rw [dn_sc F _ fun T T' φ ↦ hio T T' φ a, hy]; funext c; simp [sc, _root_.mul_assoc]⟩ }
  have h1 : I.radical = ⊤ := top_le_iff.1 (hS ▸ Ideal.span_le.2 fun f hf ↦ by
    obtain ⟨N, y, hy⟩ := h f hf
    exact ⟨N, y, hy.trans (funext fun c ↦ by simp [sc])⟩)
  obtain ⟨y, hy⟩ : (1 : B) ∈ I := by rw [Ideal.radical_eq_top.1 h1]; trivial
  exact ⟨y, hy.trans (funext fun c ↦ by simp [sc])⟩

end Transfer

section Schemes

variable {R : Type} [CommRing R] {X : Scheme.{0}} {P : Type} [SemilatticeInf P]

theorem finite_chain [Finite P] (m : ℕ) : Finite (Fin m ⥤ Pᵒᵖ) :=
  have : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  Finite.of_injective (fun c i ↦ c.obj i) fun _ _ h ↦
    CategoryTheory.Functor.ext (congrFun h) fun _ _ _ ↦ Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem res_bij (s : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (e : U = V) :
    Function.Bijective (Sec.res s h) := by
  subst e
  convert Function.bijective_id
  ext b
  exact congrArg (fun q ↦ q.hom b) (X.presheaf.map_id (op U))

variable (s : X ⟶ Sp R) (W : X.affineOpens) (u : P →o X.affineOpens) (hle : ∀ a, (u a).1 ≤ W.1)

abbrev FF (s : X ⟶ Sp R) (u : P →o X.affineOpens) : Pᵒᵖ ⥤ CommAlgCat.{0} R :=
  u.monotone.functor.op ⋙ OAff s

def rf (f : Γ(X, W.1)) (a : P) : Γ(X, (u a).1) := Sec.res s (hle a) f

theorem basicOpen_rf (f : Γ(X, W.1)) (a : P) :
    X.basicOpen (rf s W u hle f a) = (u a).1 ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE (hle a)).op

def uf (f : Γ(X, W.1)) : P →o X.affineOpens where
  toFun a := ⟨X.basicOpen (rf s W u hle f a), IsAffineOpen.basicOpen (u a).2 _⟩
  monotone' a b h := by
    change X.basicOpen _ ≤ X.basicOpen _
    rw [basicOpen_rf, basicOpen_rf]
    exact inf_le_inf_right _ (u.monotone h)

def rho (f : Γ(X, W.1)) (T : Pᵒᵖ) : (FF s u).obj T →ₐ[R] (FF s (uf s W u hle f)).obj T :=
  Sec.res s (X.basicOpen_le _)

theorem rho_nat (f : Γ(X, W.1)) {T T' : Pᵒᵖ} (φ : T ⟶ T') (b : (FF s u).obj T) :
    rho s W u hle f T' (mp (FF s u) φ b) = mp (FF s (uf s W u hle f)) φ (rho s W u hle f T b) :=
  (Sec.res_res _ _ _ b).symm.trans (Sec.res_res _ _ _ b)

def gF (f : Γ(X, W.1)) (T : Pᵒᵖ) : (FF s u).obj T := rf s W u hle f T.unop

theorem rf_nat (f : Γ(X, W.1)) (T T' : Pᵒᵖ) (φ : T ⟶ T') :
    mp (FF s u) φ (gF s W u hle f T) = gF s W u hle f T' :=
  (Sec.res_res _ _ _ f).symm

theorem loc1 (f : Γ(X, W.1)) (T : Pᵒᵖ) (y' : (FF s (uf s W u hle f)).obj T) :
    ∃ (N : ℕ) (y : (FF s u).obj T), rho s W u hle f T y =
      rho s W u hle f T (gF s W u hle f T) ^ N * y' := by
  have := IsAffineOpen.isLocalization_basicOpen (u T.unop).2 (rf s W u hle f T.unop)
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (S := Γ(X, X.basicOpen (rf s W u hle f T.unop)))
    (rf s W u hle f T.unop) y'
  exact ⟨n, a, h.symm.trans (mul_comm _ _)⟩

theorem loc2 (f : Γ(X, W.1)) (T : Pᵒᵖ) (y : (FF s u).obj T) (hy : rho s W u hle f T y = 0) :
    ∃ N : ℕ, gF s W u hle f T ^ N * y = 0 := by
  have := IsAffineOpen.isLocalization_basicOpen (u T.unop).2 (rf s W u hle f T.unop)
  obtain ⟨⟨_, N, rfl⟩, h⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (rf s W u hle f T.unop))
    Γ(X, X.basicOpen (rf s W u hle f T.unop)) y).1 hy
  exact ⟨N, h⟩

theorem uf_bij (hinf : ∀ a b, (u (a ⊓ b)).1 = (u a).1 ⊓ (u b).1) (f : Γ(X, W.1)) (a₀ : P)
    (hf : X.basicOpen f ≤ (u a₀).1) (T : Pᵒᵖ) :
    Function.Bijective (mp (FF s (uf s W u hle f)) ((th a₀).app T)) := by
  refine res_bij s _ ?_
  change X.basicOpen _ = X.basicOpen _
  rw [basicOpen_rf, basicOpen_rf]
  change _ = (u (T.unop ⊓ a₀)).1 ⊓ _
  rw [hinf, inf_assoc, inf_eq_right.2 hf]; rfl

include hle in
theorem pos [Finite P] (hC : CxSt) (hH : HtpySt) (hinf : ∀ a b, (u (a ⊓ b)).1 = (u a).1 ⊓ (u b).1)
    (hcov : ⨆ a, (u a).1 = W.1) (n : ℕ) (z : Cn (FF s u) (n + 1))
    (hz : dn (FF s u) (n + 1) z = 0) : ∃ y, dn (FF s u) n y = z := by
  have hS : Ideal.span {f : Γ(X, W.1) | ∃ a, X.basicOpen f ≤ (u a).1} = ⊤ :=
    (IsAffineOpen.self_le_iSup_basicOpen_iff W.2).1 fun x hx ↦ by
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov ▸ hx)
      obtain ⟨f, hf, hxf⟩ := IsAffineOpen.exists_basicOpen_le W.2 (V := (u a).1) ⟨x, ha⟩ (hle a ha)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, a, hf⟩, hxf⟩
  have := finite_chain (P := P) (n + 1)
  have := finite_chain (P := P) (n + 2)
  refine exact_of_span (FF s u) (fun T ↦ (Sec.res s (hle T.unop)).toRingHom)
    (fun T T' φ b ↦ (Sec.res_res _ _ _ b).symm) _ hS n z fun f ⟨a₀, hf⟩ ↦
      transfer hC (rho s W u hle f) (rho_nat s W u hle f) (gF s W u hle f)
        (rf_nat s W u hle f) (loc1 s W u hle f) (loc2 s W u hle f) n
        (fun z' hz' ↦ pointed _ a₀ (uf_bij s W u hle hinf f a₀ hf) hH n z' hz') z hz

end Schemes

section Degree0

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)

theorem chain_eq (c : Fin 1 ⥤ Pᵒᵖ) : c = (Functor.const (Fin 1)).obj (c.obj 0) :=
  CategoryTheory.Functor.ext (fun i ↦ by rw [Subsingleton.elim i 0]; rfl)
    fun _ _ _ ↦ Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem z_eq (z : Cn F 0) (c : Fin 1 ⥤ Pᵒᵖ) :
    z c = z ((Functor.const (Fin 1)).obj (c.obj 0)) :=
  eq_of_heq (congr_arg_heq z (chain_eq c))

theorem z_cocycle (z : Cn F 0) (hz : dn F 0 z = 0) {T T' : Pᵒᵖ} (φ : T ⟶ T') :
    mp F φ (z ((Functor.const (Fin 1)).obj T)) = z ((Functor.const (Fin 1)).obj T') := by
  let c : Fin 2 ⥤ Pᵒᵖ := ComposableArrows.mk₁ φ
  have e := congrFun hz c
  rw [dn_apply, Fin.sum_univ_two] at e
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at e
  have h1 : ∀ (h : T' ⟶ T') x, mp F h x = x := fun h x ↦ by
    rw [show h = 𝟙 T' from Quiver.Hom.unop_inj (Subsingleton.elim _ _), mp_id]
  have h2 : ∀ (h : T ⟶ T') x, mp F h x = mp F φ x := fun h x ↦ by
    rw [show h = φ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]
  exact (congrArg (mp F φ) (z_eq F z (face 1 c))).symm.trans
    ((h2 _ _).symm.trans ((add_neg_eq_zero.1 e).symm.trans ((h1 _ _).trans (z_eq F z (face 0 c)))))

end Degree0

theorem main : CxSt → HtpySt → AffAcycSt := by
  intro hC hH R _ X s W P _ _ u hle hinf hcov F aug
  refine ⟨(injective_iff_map_eq_zero aug).2 fun b hb ↦
      TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun a ↦ (u a).1) W.1 (fun a ↦ homOfLE (hle a)) hcov.ge b 0 fun a ↦
        (congrFun hb ((Functor.const (Fin 1)).obj (op a))).trans (map_zero _).symm,
    fun z ↦ ⟨fun hz ↦ ?_, ?_⟩, fun n z ↦ ⟨fun hz ↦ pos s W u hle hC hH hinf hcov n z hz, ?_⟩⟩
  · obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun a ↦ (u a).1) W.1
      (fun a ↦ homOfLE (hle a)) hcov.ge (fun a ↦ z ((Functor.const (Fin 1)).obj (op a))) fun i j ↦ by
        refine (res_bij s (le_of_eq (hinf i j)) (hinf i j).symm).1 ?_
        exact ((Sec.res_res s inf_le_left (le_of_eq (hinf i j)) _).symm.trans
            (z_cocycle F z hz (homOfLE (inf_le_left : i ⊓ j ≤ i)).op)).trans
          ((Sec.res_res s inf_le_right (le_of_eq (hinf i j)) _).symm.trans
            (z_cocycle F z hz (homOfLE (inf_le_right : i ⊓ j ≤ j)).op)).symm
    exact ⟨t, funext fun c ↦ (ht (c.obj (Fin.last 0)).unop).trans (z_eq F z c).symm⟩
  · rintro ⟨b, rfl⟩
    funext c
    rw [dn_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
    exact add_neg_eq_zero.2 (((Sec.res_res _ _ _ b).symm).trans (Sec.res_res _ _ _ b))
  · rintro ⟨y, rfl⟩; exact LinearMap.congr_fun ((hC R Pᵒᵖ F).1 n) y

end GlobalTheory.CompanionTheory.AffAcyc
