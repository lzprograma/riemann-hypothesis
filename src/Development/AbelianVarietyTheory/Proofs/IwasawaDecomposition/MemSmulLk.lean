module

public import Formalism.LocalToGlobal.HermitianColumns.SymAll
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms Matrix

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

abbrev co (S : HSpace E) {n : ℕ} (h : S.rank = n) : S.V ≃ₗ[E] (Fin n → E) :=
  S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

abbrev gr (S : HSpace E) {n : ℕ} (h : S.rank = n) : Matrix (Fin n) (Fin n) E :=
  S.gram.reindex (finCongr h) (finCongr h)

theorem hT_co (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (x y : S.V) :
    S.hT x y = hform (hc.sig : E →+* E) (gr S h) (co S h x) (co S h y) := by
  subst h
  rw [Formalism.L2.Herm.hT_crd hc]
  rfl

abbrev lc (S : HSpace E) {n : ℕ} (h : S.rank = n) (L : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (Fin n → E) :=
  L.map (((co S h : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))

theorem mem_lc (S : HSpace E) {n : ℕ} (h : S.rank = n) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    co S h x ∈ lc S h L ↔ x ∈ L := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := (co S h).injective e
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem dual_co (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (L : Submodule (𝓞 E) S.V) :
    lc S h (Formalism.HermitianLatticesTheory.dual S.hT L) = dualL (hc.sig : E →+* E) (gr S h) (lc S h L) := by
  subst h
  have key : ((lc S rfl (Formalism.HermitianLatticesTheory.dual S.hT L) : Submodule (𝓞 E) (Fin S.rank → E)) : Set (Fin S.rank → E)) =
      dualSet (hc.sig : E →+* E) (gr S rfl) (lc S rfl L) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩ s ⟨y, hy, rfl⟩
      have := (Formalism.L2.Herm.mem_dual S L x).1 hx y hy
      rw [hT_co hc S rfl] at this
      exact this
    · intro ht
      refine ⟨(co S rfl).symm t, ?_, (co S rfl).apply_symm_apply t⟩
      refine (Formalism.L2.Herm.mem_dual S L _).2 fun y hy => ?_
      rw [hT_co hc S rfl]
      have := ht (co S rfl y) ⟨y, hy, rfl⟩
      rwa [show co S rfl ((co S rfl).symm t) = t from (co S rfl).apply_symm_apply t]
  unfold dualL
  rw [← key, Submodule.span_eq]

theorem lc_sup (S : HSpace E) {n : ℕ} (h : S.rank = n) (L M : Submodule (𝓞 E) S.V) :
    lc S h (L ⊔ M) = lc S h L ⊔ lc S h M := Submodule.map_sup _ _ _

theorem lc_smul (S : HSpace E) {n : ℕ} (h : S.rank = n) (P : Ideal (𝓞 E)) (L : Submodule (𝓞 E) S.V) :
    lc S h (P • L) = P • lc S h L := Submodule.map_smul'' _ _ _

def lin (S : HSpace E) {n : ℕ} (h : S.rank = n) : GL (Fin n) E ≃* (S.V ≃ₗ[E] S.V) :=
  (reGL h.symm E).trans (Formalism.L2.Herm.toGLb S.frame).symm

theorem reGL_lin (S : HSpace E) {n : ℕ} (h : S.rank = n) (γ : GL (Fin n) E) :
    reGL h E (Formalism.L2.Herm.toGLb S.frame (lin S h γ)) = γ := by
  subst h
  ext a b
  simp [lin, reGL]

theorem co_lin (S : HSpace E) {n : ℕ} (h : S.rank = n) (γ : GL (Fin n) E) (x : S.V) :
    co S h (lin S h γ x) = γ.1 *ᵥ co S h x := by
  subst h
  have e : Formalism.L2.Herm.toGLb S.frame (lin S rfl γ) = γ := by
    have := reGL_lin S rfl γ
    have e0 : ∀ g : GL (Fin S.rank) E, reGL rfl E g = g := fun g => by
      ext a b
      simp [reGL]
    rwa [e0] at this
  have e2 : S.frame.equivFun (lin S rfl γ x) = (Formalism.L2.Herm.toGLb S.frame (lin S rfl γ)).1 *ᵥ S.frame.equivFun x :=
    (LinearMap.toMatrix_mulVec_repr S.frame S.frame ((lin S rfl γ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) x).symm
  rw [e] at e2
  ext j
  simpa using congrFun e2 j

theorem lin_mem (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (γ : GL (Fin n) E)
    (hγ : γ ∈ UJ (hc.sig : E →+* E) (gr S h)) : lin S h γ ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  intro x y
  rw [hT_co hc S h, hT_co hc S h x y, co_lin, co_lin]
  have e1 : ∀ (s : E →+* E) (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E), hform s J a b = (s ∘ a) ⬝ᵥ (J *ᵥ b) := fun s J a b => by
    simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp, mul_assoc]
  have e2 : ∀ (s : E →+* E) (J g : Matrix (Fin n) (Fin n) E) (a b : Fin n → E),
      hform s J (g *ᵥ a) (g *ᵥ b) = hform s (cT s g * J * g) a b := fun s J g a b => by
    have h : s ∘ (g *ᵥ a) = (g.map s) *ᵥ (s ∘ a) := by
      funext i
      exact RingHom.map_mulVec s g a i
    rw [e1, e1, h, cT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (s ∘ a), Matrix.vecMul_transpose]
  rw [e2]
  exact congrArg (fun J => hform (hc.sig : E →+* E) J (co S h x) (co S h y)) hγ

end Gen

section Dd

variable {D : D7} {u : D.what₂.Word}

theorem mem_Ld (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (z : (D.sp.X i).V) :
    z ∈ Formalism.L2.Herm.Ld D u i c ↔ crdN D i hi z ∈ Ld D u i hi c := by
  have e : lc (D.sp.X i) (rankN D i hi) (Formalism.L2.Herm.Ld D u i c) = Ld D u i hi c :=
    dual_co D.sp.cm (D.sp.X i) (rankN D i hi) (D.clsLat u i c)
  rw [← e]
  exact (mem_lc (D.sp.X i) (rankN D i hi) _ z).symm

theorem mem_Lk (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (z : (D.sp.X i).V) : z ∈ Formalism.L2.Herm.Lk D u (A.Pv v) i c ↔ crdN D i hi z ∈ Lk A i hi v c := by
  have e : lc (D.sp.X i) (rankN D i hi) (Formalism.L2.Herm.Lk D u (A.Pv v) i c) = Lk A i hi v c := by
    rw [lc_sup, lc_smul]
    exact congrArg₂ (· ⊔ ·) rfl (congrArg (A.Pv v • ·) (dual_co D.sp.cm (D.sp.X i) (rankN D i hi) (D.clsLat u i c)))
  rw [← e]
  exact (mem_lc (D.sp.X i) (rankN D i hi) _ z).symm

theorem crdN_osmul (i : ℕ) (hi : i ≤ D.R.m) (a : 𝓞 D.host.E) (z : (D.sp.X i).V) :
    crdN D i hi (a • z) = a • crdN D i hi z :=
  LinearMap.map_smul_of_tower (crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) a z

def toLd (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) : Formalism.L2.Herm.Ld D u i c →+ Ld D u i hi c where
  toFun z := ⟨crdN D i hi z.1, (mem_Ld i hi c z.1).1 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def toLk (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Formalism.L2.Herm.Lk D u (A.Pv v) i c →+ Lk A i hi v c where
  toFun z := ⟨crdN D i hi z.1, (mem_Lk A i hi v c z.1).1 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

variable (A : AtTTied u) (P : ∀ i hi, LvTied u A i hi)


open Classical in
def prH (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : Formalism.L2.Herm.Ld D u i c →+ (D.fm u).lv i v c :=
  if hi : i ≤ D.R.m then ((P i hi).pr v c).comp (toLd i hi c) else 0


open Classical in
def prkH (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Formalism.L2.Herm.Lk D u (A.Pv v) i c →+ (D.fm u).lk i v c :=
  if hi : i ≤ D.R.m then ((P i hi).prk v c).comp (toLk A i hi v c) else 0

theorem prH_eq {i : ℕ} (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : Formalism.L2.Herm.Ld D u i c) :
    prH A P i v c z = (P i hi).pr v c (toLd i hi c z) := by
  simp [prH, hi]

theorem prkH_eq {i : ℕ} (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : Formalism.L2.Herm.Lk D u (A.Pv v) i c) :
    prkH A P i v c z = (P i hi).prk v c (toLk A i hi v c z) := by
  simp [prkH, hi]

theorem toLd_smul {i : ℕ} (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (a : 𝓞 D.host.E) (z : Formalism.L2.Herm.Ld D u i c) :
    toLd i hi c (a • z) = a • toLd i hi c z := Subtype.ext (crdN_osmul i hi a z.1)

theorem toLd_surj {i : ℕ} (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) : Function.Surjective (toLd (u := u) i hi c) := fun z =>
  ⟨⟨(crdN D i hi).symm z.1, (mem_Ld i hi c _).2 (by simpa using z.2)⟩, Subtype.ext (by simp [toLd])⟩

end Dd

section Mk

variable {D : D7} {u : D.what₂.Word} (A : AtTTied u) (P : ∀ i hi, LvTied u A i hi)

def UpCl (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : Formalism.L2.Herm.Ld D u i c) (γ : Formalism.L2.Herm.GX D i) : Prop :=
  Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap γ.1 (D.clsLat u i ((D.fm u).up i v c (prH A P i v c y)))) (D.clsLat u i c) ∧
    Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap γ.1 (D.clsLat u i ((D.fm u).up i v c (prH A P i v c y)))) =
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Herm.Ld D u i c) ∧
    Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap γ.1 (Formalism.L2.Herm.Ld D u i ((D.fm u).up i v c (prH A P i v c y)))) =
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Herm.Ld D u i c ⊔
        Submodule.span (𝓞 D.host.E) {((D.mem u).A.T : D.host.E)⁻¹ • (y : (D.sp.X i).V)}) ∧
    (∀ (z : Formalism.L2.Herm.Ld D u i ((D.fm u).up i v c (prH A P i v c y)))
      (hz : ((D.mem u).A.T : D.host.E) • γ.1 (z : (D.sp.X i).V) ∈ Formalism.L2.Herm.Ld D u i c),
      (D.fm u).fv i v _ (prH A P i v _ z) = (D.fm u).fv i v c (prH A P i v c ⟨_, hz⟩)) ∧
    (∀ v', v' ≠ v → ∀ (z : Formalism.L2.Herm.Ld D u i ((D.fm u).up i v c (prH A P i v c y)))
      (hz : γ.1 (z : (D.sp.X i).V) ∈ Formalism.L2.Herm.Ld D u i c),
      (D.fm u).fv i v' _ (prH A P i v' _ z) = (D.fm u).fv i v' c (prH A P i v' c ⟨_, hz⟩))

def DnCl (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (γ : Formalism.L2.Herm.GX D i) : Prop :=
  Formalism.L2.Herm.SameOff (A.Pv v) (Formalism.HermitianLatticesTheory.gmap γ.1 (D.clsLat u i ((D.fm u).dn i v c g))) (D.clsLat u i c) ∧
    Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.HermitianLatticesTheory.gmap γ.1 (Formalism.L2.Herm.Ld D u i ((D.fm u).dn i v c g))) =
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (D.clsLat u i c) ∧
    (∀ (z : Formalism.L2.Herm.Ld D u i ((D.fm u).dn i v c g))
      (hz : γ.1 (z : (D.sp.X i).V) ∈ Formalism.L2.Herm.Lk D u (A.Pv v) i c),
      (D.fm u).fv i v _ (prH A P i v _ z) = g (prkH A P i v c ⟨_, hz⟩)) ∧
    (∀ v', v' ≠ v → ∀ (z : Formalism.L2.Herm.Ld D u i ((D.fm u).dn i v c g))
      (hz : γ.1 (z : (D.sp.X i).V) ∈ Formalism.L2.Herm.Ld D u i c),
      (D.fm u).fv i v' _ (prH A P i v' _ z) = (D.fm u).fv i v' c (prH A P i v' c ⟨_, hz⟩))

def DilCl (i : ℕ) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i) (γ : Formalism.L2.Herm.GX D i) : Prop :=
  Formalism.HermitianLatticesTheory.gmap γ.1 (D.clsLat u i ((D.fm u).dil i v a c)) = D.clsLat u i c ∧
    (∀ (z : Formalism.L2.Herm.Ld D u i ((D.fm u).dil i v a c))
      (hz : γ.1 (z : (D.sp.X i).V) ∈ Formalism.L2.Herm.Ld D u i c),
      (D.fm u).fv i v _ (prH A P i v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c (prH A P i v c ⟨_, hz⟩)) ∧
    (∀ v', v' ≠ v → ∀ (z : Formalism.L2.Herm.Ld D u i ((D.fm u).dil i v a c))
      (hz : γ.1 (z : (D.sp.X i).V) ∈ Formalism.L2.Herm.Ld D u i c),
      (D.fm u).fv i v' _ (prH A P i v' _ z) = (D.fm u).fv i v' c (prH A P i v' c ⟨_, hz⟩))

def SeenCl : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.E) (y : D.what₂.LL),
      D.what₂.embLL y = D.host.emb (D.eTau ((D.fm u).tauOf w v)).1 (x : D.host.E) →
      ((0 : WithTop ℤ) < D.what₂.places.val w y ↔
        x ∈ (if (D.fm u).seenP w then A.Pv v else Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v)))

def DiscCl : Prop :=
  ∀ i, i ≤ D.R.m → ∀ c : (D.mem u).C.cls i,
    Nonempty ((Formalism.L2.Herm.Ld D u i c ⧸ (D.clsLat u i c).comap (Formalism.L2.Herm.Ld D u i c).subtype) ≃ₗ[𝓞 D.host.E]
      (𝓞 D.host.E ⧸ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)}))

def gx (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) : Formalism.L2.Herm.GX D i :=
  ⟨lin (D.sp.X i) (rankN D i hi) γ.1, lin_mem D.sp.cm (D.sp.X i) (rankN D i hi) γ.1 γ.2⟩

theorem crdN_gx (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (x : (D.sp.X i).V) :
    crdN D i hi ((gx i hi γ).1 x) = γ.1.1 *ᵥ crdN D i hi x :=
  co_lin (D.sp.X i) (rankN D i hi) γ.1 x

theorem lc_gmap (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    (Formalism.HermitianLatticesTheory.gmap (gx i hi γ).1 L).map ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) =
      Formalism.L2.Forms.mulLat γ.1.1 (L.map ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Formalism.L2.Forms.mulLat, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, (crdN_gx i hi γ y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, crdN_gx i hi γ y⟩

variable {e : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}}
  {eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (e v).1.asIdeal)}



def mkAtT (he : A.eV = e)
    (hF : ∀ v (a : 𝓞 D.host.F), eF v (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a)
    (hseen : SeenCl A) (hdisc : DiscCl (u := u))
    (upG : ∀ i v (c : (D.mem u).C.cls i), Formalism.L2.Herm.Ld D u i c → Formalism.L2.Herm.GX D i)
    (hup : ∀ i, i ≤ D.R.m → ∀ v c (y : Formalism.L2.Herm.Ld D u i c), (D.fm u).fv i v c (prH A P i v c y) = 1 →
      UpCl A P i v c y (upG i v c y))
    (dnG : ∀ i v (c : (D.mem u).C.cls i), Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) → Formalism.L2.Herm.GX D i)
    (hdn : ∀ i, i ≤ D.R.m → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
      DnCl A P i v c g (dnG i v c g))
    (dilG : ∀ i v, ((D.mem u).A.Fv v)ˣ → (D.mem u).C.cls i → Formalism.L2.Herm.GX D i)
    (hdil : ∀ i, i ≤ D.R.m → ∀ v a c, DilCl A P i v a c (dilG i v a c))
    (lattice₂ : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V)
    (levP : Formalism.L2.Herm.StepLevel0 D.sp.cm D.sp.X' D.host.g (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0))
    (clsP : Formalism.L2.Herm.ClassTie D.sp.cm D.sp.X' (Formalism.L2.Herm.crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ lattice₂)
    {K : ClsPTied u} (Tl : TilTied u A K (P D.R.m le_rfl))
    (hlat : ∀ c, K.lat c = (lattice₂ c).map ((crdP D : D.sp.X'.V →ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E)).restrictScalars (𝓞 D.host.E))) :
    Formalism.L2.Herm.AtT D u e eF where
  piU := A.piU
  piU_K := A.piU_K
  piU_norm := A.piU_norm
  piU_cong := A.piU_cong
  Pv := A.Pv
  Pv_max v := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  Pv_pi v := A.res_pi v
  Pv_over v := by
    ext x
    rw [Ideal.mem_comap, ← he]
    exact ((A.res_v v x).symm)
  res := A.res
  res_ker _ := rfl
  res_F := hF
  seen := hseen
  disc := hdisc
  pr := prH A P
  pr_surj i hi v c x := by
    obtain ⟨z, rfl⟩ := (P i hi).pr_surj v c x
    obtain ⟨y, rfl⟩ := toLd_surj hi c z
    exact ⟨y, prH_eq A P hi v c y⟩
  pr_smul i v c a y := by
    by_cases hi : i ≤ D.R.m
    · rw [prH_eq A P hi, prH_eq A P hi, toLd_smul, (P i hi).pr_smul]
    · simp [prH, hi]
  prk := prkH A P
  upG := upG
  dnG := dnG
  dilG := dilG
  lattice₂ := lattice₂
  levP := levP
  clsP := clsP
  z0 := (crdN D D.R.m le_rfl).symm Tl.z0
  tilG c := gx D.R.m le_rfl (Tl.ga c)

def AdOf {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (u : D.what₂.Word) :
    ∀ i, (D.mem u).C.cls i → (D.mem u).C.cls i → Formalism.L2.Herm.GX D i → (D.mem u).A.vT → Prop
  | 0, c, c', γ, v => Formalism.L2.Herm.Ad0S D H u c c' γ v
  | i + 1, c, c', γ, v => ∀ hm : i + 1 ≤ D.R.m, Formalism.L2.Herm.AdIS D H u (i + 1) (Nat.succ_pos i) hm c c' γ v

def AdC {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m)
    (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (w : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  (∀ h : i = 0 ∨ i = D.R.m, Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) (T.cls i hi h).lev.U
    ((T.cls i hi h).y c).1 ((T.cls i hi h).y c').1 γ w) ∧
  ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m), ∃ hβ : chOf i c' = chOf i c,
    Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) (T.ch i h1 h2 (chOf i c)).lev.U
      ((T.ch i h1 h2 (chOf i c)).y ⟨c, rfl⟩).1 ((T.ch i h1 h2 (chOf i c)).y ⟨c', hβ⟩).1 γ w

theorem localization_map₂ {i : ℕ} (hi : i ≤ D.R.m) (q : Ideal (𝓞 D.host.E)) [q.IsPrime] (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    (Formalism.HermitianLatticesTheory.localization₂ q L).map ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) =
      Formalism.HermitianLatticesTheory.localization₂ q (L.map ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))) := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, ⟨_, hy, crdN_osmul i hi s y⟩⟩
  · rintro ⟨s, hs, ⟨y, hy, e⟩⟩
    refine ⟨(crdN D i hi).symm x, ⟨s, hs, ?_⟩, (crdN D i hi).apply_symm_apply x⟩
    have e2 : s • (crdN D i hi).symm x = y := by
      apply (crdN D i hi).injective
      rw [crdN_osmul, LinearEquiv.apply_symm_apply]
      exact e.symm
    rw [e2]
    exact hy

end Mk

end GlobalTheory.Mem.Col2.HAt
