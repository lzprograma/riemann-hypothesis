module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Pairing

variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X} {v : Sp (DualNumber k) ⟶ t.G.left}

theorem epsZero_comp_of_isTanAtG (hv : IsTanAtG t x v) : sec (epsZero k) ≫ v = x ≫ unitSec t.G :=
  hv.2

def tanForm (hv : IsTanAtG t x v) :
    (Scheme.Modules.pullback x).obj (omega t.G) ⟶ GlobalTheory.structureModule (Sp k) :=
  baseMap (π := t.G.hom) (φ := v) (f := x) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv) ≫ (epsIso k).hom

def tanEv (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(omega t.G, V)) : k :=
  (Scheme.ΓSpecIso (.of k)).hom ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s))

theorem tanEv_add (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s s' : Γ(omega t.G, V)) :
    tanEv t hv h (s + s') = tanEv t hv h s + tanEv t hv h s' := by
  simp only [tanEv, map_add (f := _)]
  exact map_add (Scheme.ΓSpecIso (.of k)).hom.hom _ _

theorem tanEv_smul (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, V)) (s : Γ(omega t.G, V)) :
    tanEv t hv h (a • s) = (Scheme.ΓSpecIso (.of k)).hom (x.appLE V ⊤ h a) * tanEv t hv h s := by
  have e2 : (tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h (a • s)) =
      x.appLE V ⊤ h a • (tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) := by
    have e : pullbackSections x (omega t.G) h (a • s) = x.appLE V ⊤ h a • pullbackSections x (omega t.G) h s :=
      QCoh.pullbackSections_smul x (omega t.G) h a s
    rw [e]
    exact Scheme.Modules.Hom.app_smul _ _ _
  unfold tanEv
  rw [e2]
  exact map_mul (Scheme.ΓSpecIso (.of k)).hom.hom _ _

theorem tanEv_resM (hv : IsTanAtG t x v) {V V' : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V') (h' : V' ≤ V) (s : Γ(omega t.G, V)) :
    tanEv t hv h (resM _ h' s) = tanEv t hv (h.trans (x.preimage_mono h')) s := by
  unfold tanEv
  congr 2
  exact QCoh.pullbackSections_res x (omega t.G) h h' s

theorem tanEv_dUnit (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) (hv' : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(t.G.left, W)) :
    tanEv t hv h (dUnit t.G hW f) = ((Scheme.ΓSpecIso (.of (DualNumber k))).hom (v.appLE W ⊤ hv' f)).snd := by
  have h1 : (baseMap (π := t.G.hom) (φ := v) (f := x) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv)).app ⊤
      (pullbackSections x (conormal (unitSec t.G)) h (d (sec_hom η[t.G]) hW f)) =
      d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) (v.appLE W ⊤ hv' f) :=
    baseMap_d (sec_hom η) (sec_hom (epsZero k)) hv.left (epsZero_comp_of_isTanAtG t hv) hW h
      (le_preimage_top (LieVB.sec (epsZero k)) ⊤) hv' f
  have h2 (P Q : Γ(Sp (DualNumber k), ⊤)) : d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) (P * Q) =
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤) P • d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) Q +
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤) Q • d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) P :=
    d_mul (sec_hom (epsZero k)) (le_preimage_top (LieVB.sec (epsZero k)) ⊤) P Q
  have h3 (a : Γ(Sp k, ⊤)) : d (sec_hom (epsZero k)) (le_preimage_top _ ⊤)
      ((specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) a) = 0 :=
    d_base (sec_hom (epsZero k)) (le_preimage_top (LieVB.sec (epsZero k)) ⊤)
      (le_preimage_top (specO k (DualNumber k)).hom ⊤) a
  have hB (c : k) : (specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k c) =
      (Scheme.ΓSpecIso (.of (DualNumber k))).inv (algebraMap k (DualNumber k) c) := by
    rw [appLE_top]
    have e := congrArg (fun g => g.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    exact e.symm
  have hP (a : Γ(Sp k, ⊤)) :
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤) ((specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) a) = a := by
    rw [appLE_top, appLE_top]
    have e := congrArg (fun g : Sp k ⟶ Sp k => g.appTop a) (sec_hom (epsZero k))
    simp at e
    exact e
  set F := v.appLE W ⊤ hv' f
  set D := (Scheme.ΓSpecIso (.of (DualNumber k))).hom F with hD
  have hdec : F = (specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k D.fst) +
      (specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k D.snd) * epsFn k := by
    rw [hB, hB, epsFn, ← map_mul, ← map_add (f := _)]
    have e : algebraMap k (DualNumber k) D.fst + algebraMap k (DualNumber k) D.snd * DualNumber.eps = D := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [e, hD, Iso.hom_inv_id_apply]
  have hdF : d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) F =
      (sec (epsZero k)).appLE ⊤ ⊤ (le_preimage_top _ ⊤)
          ((specO k (DualNumber k)).hom.appLE ⊤ ⊤ (le_preimage_top _ ⊤) (cst k D.snd)) •
        d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) (epsFn k) := by
    rw [hdec, map_add (f := _), h3, h2, h3, smul_zero, add_zero, zero_add]
  have h4 : (tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h (dUnit t.G hW f)) =
      (epsIso k).hom.app ⊤ (d (sec_hom (epsZero k)) (le_preimage_top _ ⊤) F) := by
    rw [← h1]
    exact (QCoh.app_app _ _ _ _).symm
  rw [tanEv, h4, hdF]
  erw [Scheme.Modules.Hom.app_smul, epsIso_d, hP]
  erw [smul_eq_mul, _root_.mul_one]
  simp

end Pairing

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

abbrev Mdl.om (B : Mdl Y i₀) : B.X.Modules := omega B.t.G

structure Lat (B : Mdl Y i₀) : Type where

  N : VB.Sub B.om

  free : ∀ x : B.X, ∃ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(N.toMod, V)), x ∈ V ∧ VB.IsFrame m

  gen : ∀ V : B.X.Opens, V ≤ B.genO → N.sec V = ⊤

def rangeSub {X : Scheme.{0}} {F G : X.Modules} (θ : F ⟶ G) [Mono θ] : VB.Sub G where
  sec V := LinearMap.range (QCoh.appLinear θ V)
  res_mem := by
    rintro V V' h _ ⟨s, rfl⟩
    exact ⟨resM F h s, app_resM θ h s⟩
  mem_of_local {V s} hs := by
    choose U hU hx t ht using fun x : V => hs x x.2
    have hc : V ≤ iSup U := fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
    have ht' (x : V) : θ.app _ (t x) = resM G (hU x) s := ht x
    obtain ⟨r, hr⟩ := Twist.exists_sec_of_cover U hU hc t fun x y => QCoh.injective_app_of_mono θ _ (by
      rw [app_resM, app_resM, ht', ht', resM_resM, resM_resM])
    exact ⟨r, Twist.sec_ext_of_cover U hU hc fun x =>
      (app_resM θ _ r).symm.trans ((congrArg _ (hr x)).trans (ht' x))⟩

theorem isIso_lift_rangeSub {X : Scheme.{0}} {F G : X.Modules} (θ : F ⟶ G) [Mono θ] :
    IsIso ((rangeSub θ).lift θ fun _ s => ⟨s, rfl⟩) := by
  set φ := (rangeSub θ).lift θ fun _ s => ⟨s, rfl⟩
  have hfac : φ ≫ (rangeSub θ).incl = θ := (rangeSub θ).lift_incl θ _
  have hsurj (V : X.Opens) (s : Γ((rangeSub θ).toMod, V)) : ∃ r, φ.app V r = s := by
    obtain ⟨r, hr⟩ := (rangeSub θ).incl_app_mem s
    refine ⟨r, (rangeSub θ).incl_app_injective V ?_⟩
    rw [QCoh.app_app, hfac]
    simpa using hr
  have : Mono φ := mono_of_mono_fac hfac
  have : Epi φ := ⟨fun {Z} g₁ g₂ h => by
    ext V s
    obtain ⟨r, rfl⟩ := hsurj V s
    rw [QCoh.app_app, QCoh.app_app, h]⟩
  exact isIso_of_mono_of_epi φ

namespace Lat

variable {B : Mdl Y i₀}

def ofBundle {F : B.X.Modules} (θ : F ⟶ B.om) [Mono θ]
    (hF : ∀ x : B.X, ∃ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(F, V)), x ∈ V ∧ VB.IsFrame m)
    (hθ : ∀ V : B.X.Opens, V ≤ B.genO → Function.Surjective (θ.app V)) : Lat B where
  N := rangeSub θ
  free x :=
    have ⟨V, n, _, hx, hm⟩ := hF x
    have := isIso_lift_rangeSub θ
    ⟨V, n, _, hx, hm.map_iso ((rangeSub θ).lift θ fun _ s => ⟨s, rfl⟩)⟩
  gen V h := LinearMap.range_eq_top.2 (hθ V h)


variable (B) in
def top : Lat B :=
  ofBundle (𝟙 _) (have := B.t.semi; have := B.t.semi.smooth; exists_isFrame_omega B.t.G) fun _ _ s => ⟨s, rfl⟩

def IsTop (L : Lat B) : Prop := ∀ V, L.N.sec V = ⊤

theorem ext {L L' : Lat B} (h : ∀ V, L.N.sec V = L'.N.sec V) : L = L' := by
  obtain ⟨⟨N, r, m⟩, f, g⟩ := L
  obtain ⟨⟨N', r', m'⟩, f', g'⟩ := L'
  obtain rfl : N = N' := funext h
  rfl

end Lat


variable (Y i₀) in
structure Step : Type where

  B : Mdl Y i₀

  L : Lat B

  σ : E →+* ℂ

  k : ℕ

  le : k ≤ Dw.mult σ




open Classical in
def allSteps {B : Mdl Y i₀} (L : Lat B) : Finset (Step Y i₀) :=
  Finset.univ.image fun q : Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1) => ⟨B, L, q.1, q.2, Nat.lt_succ_iff.1 q.2.2⟩

theorem mem_allSteps {B : Mdl Y i₀} {L : Lat B} {t : Step Y i₀} :
    t ∈ allSteps L ↔ ∃ σ r hr, t = ⟨B, L, σ, r, hr⟩ := by
  classical
  constructor
  · rintro h
    obtain ⟨⟨σ, r⟩, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨σ, r, _, rfl⟩
  · rintro ⟨σ, r, hr, rfl⟩
    exact Finset.mem_image.2 ⟨⟨σ, ⟨r, Nat.lt_succ_iff.2 hr⟩⟩, Finset.mem_univ _, rfl⟩

def Step.admitted (P : ∀ B : Mdl Y i₀, Lat B → Prop) (Z : Mdl Y i₀) (t : Step Y i₀) : Prop :=
  (t.B = Z ∨ ∃ f, IsMap Z t.B f) ∧ (t.L.IsTop ∨ P t.B t.L)

def FlagFam (P : ∀ B : Mdl Y i₀, Lat B → Prop) (Z : Mdl Y i₀) : Type :=
  {s : Finset (Step Y i₀) // ∀ t ∈ s, t.admitted P Z}

namespace FlagFam

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop}

def empty (Z : Mdl Y i₀) : FlagFam P Z := ⟨∅, by simp⟩

def full {Z : Mdl Y i₀} (L : Lat Z) (h : L.IsTop ∨ P Z L) : FlagFam P Z :=
  ⟨allSteps L, fun t ht => by
    obtain ⟨σ, r, hr, rfl⟩ := mem_allSteps.1 ht
    exact ⟨.inl rfl, h⟩⟩

end FlagFam

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}


end GlobalTheory.LocM
