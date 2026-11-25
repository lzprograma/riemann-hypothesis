module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NonemptyLinearEquivOfPiFinPowFinite
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticePointUniversal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumber
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RelOfTorsion
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionOne
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValues
import Development.WeilBound.CoreStatements.HodgeTatePoints.MhBase
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.TwDer

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

section Rel
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))} (U : Γ.G.left.Opens)
  {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

theorem fst_comp_eq_unit (ht : Γ.IsTorsionAlong G x N i) {y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left}
    (y1 : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))))
    {v : ob x V ⟶ G} (y3 : y ≫ i = v.left) (h1 : zsec x ≫ v = 1) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y = η[Γ.G].left :=
  GlobalTheory.CompanionTheory.Ar.BT.Tan.fst_comp_eq_unit Γ ht y1 y3 h1

theorem mem_of_fst_comp {y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left}
    (e : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R V).toRingHom) ≫ y = η[Γ.G].left)
    (hU : ∀ z, η[Γ.G].left z ∈ U) (z) : y z ∈ U :=
  GlobalTheory.CompanionTheory.Ar.BT.Tan.mem_of_fst_comp Γ U e hU z

theorem rel_exists_open (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)]
    (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) :
    ∃ v : ob x V ⟶ G, zsec x ≫ v = 1 ∧ v ^ N = 1 ∧ TanRel Γ i j ψ v :=
  GlobalTheory.CompanionTheory.Ar.BT.Tan.rel_exists_open Γ U ht hj hU ψ

theorem rel_eq_open (ht : Γ.IsTorsionAlong G x N i) (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)]
    {ψ : omega (Γ.btOrder ⊤) →ₗ[R] V} {v v' : ob x V ⟶ G}
    (h : TanRel Γ i j ψ v) (h' : TanRel Γ i j ψ v') (h1 : zsec x ≫ v = 1) (h1' : zsec x ≫ v' = 1) : v = v' :=
  GlobalTheory.CompanionTheory.Ar.BT.Tan.rel_eq_open Γ U ht hU h h' h1 h1'

end Rel

section Core
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
  {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))} (U : Γ.G.left.Opens)
  {P : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

theorem exists_theta_open (ht : Γ.IsTorsionAlong G x N i) (hj : Γ.IsEmb (Γ.btOrder ⊤) j)
    (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)]
    (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1)
    (huniv : ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (v : ob x V ⟶ G),
      zsec x ≫ v = 1 → ∃! φ : P →ₗ[R] V, hom x φ ≫ u = v) :
    ∃ θ : P →ₗ[R] omega (Γ.btOrder ⊤), Function.Surjective θ ∧ N • θ = 0 ∧
      ∀ (V : Type) [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (φ : P →ₗ[R] V), N • φ = 0 →
        ∃ ψ : omega (Γ.btOrder ⊤) →ₗ[R] V, ψ ∘ₗ θ = φ ∧ TanRel Γ i j ψ (hom x φ ≫ u) :=
  GlobalTheory.CompanionTheory.Ar.BT.Tan.exists_theta_open Γ U ht hj hU u hu huniv

end Core

theorem omega_open {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (ht : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L]
    [Module.Projective R L] (M : LieModel G x L) {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (U : Γ.G.left.Opens) (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)] :
    ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), Function.Surjective θ ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f.1.1 : T → R) → (θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) → v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e))) :=
  GlobalTheory.CompanionTheory.Ar.BT.Tan.omega_open Γ ht M hj U hU

end GlobalTheory.CompanionTheory.Ar.HT.TwDer

namespace GlobalTheory.CompanionTheory.Ar.HT.TwDer

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

section Der
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} (N : ℕ) (i : Γ.G.left ⟶ G.left)
  {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L)

abbrev Q (R : Type) [CommRing R] (N : ℕ) : Type := R ⧸ Ideal.span {(N : R)}

def IsTanPt (e : L) (v : Spec (CommRingCat.of (DualNumber (Q R N))) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
    v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left

def Der (f : T → R) (w : Module.Dual R L) : Prop :=
  ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s f ∧ ∀ e : L,
    ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
        (M.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (f 1)) +
        TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e))

theorem valAt_add' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a b : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a + b) = valAt y ⊤ le_top a + valAt y ⊤ le_top b := by
  simp [valAt]

theorem valAt_mul' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a b : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a * b) = valAt y ⊤ le_top a * valAt y ⊤ le_top b := by
  simp [valAt]

def cst (r : R) : Γ(Γ.G.left, ⊤) :=
  Γ.G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

theorem valAt_cst {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (φ : R →+* B)
    (h : y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom φ)) (r : R) : valAt y ⊤ le_top (cst Γ r) = φ r :=
  ValEmb.valAt_pull Γ.G.hom y φ h r

theorem hasValues_cst (r : R) : Γ.HasValues (cst Γ r) (fun _ => r) := fun t =>
  valAt_cst Γ (Γ.pt t).left (algebraMap R (FractionRing R)) (Over.w (Γ.pt t)) r

theorem der_const (r : R) (h : ∀ e : L, ∃ v, IsTanPt Γ N i M e v) : Der Γ N i M (fun _ => r) 0 := by
  refine ⟨cst Γ r, hasValues_cst Γ r, fun e => ?_⟩
  obtain ⟨v, h1, h2⟩ := h e
  refine ⟨v, h1, h2, ?_⟩
  rw [valAt_cst Γ v _ h1]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {Γ N i M}

theorem der_add_mul (hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v')
    {f g : T → R} {w w' : Module.Dual R L} (hf : Der Γ N i M f w) (hg : Der Γ N i M g w') :
    Der Γ N i M (f + g) (w + w') ∧ Der Γ N i M (f * g) (f 1 • w' + g 1 • w) := by
  obtain ⟨s, hs, hv⟩ := hf
  obtain ⟨s', hs', hv'⟩ := hg
  constructor
  · refine ⟨s + s', fun t => ?_, fun e => ?_⟩
    · rw [valAt_add', hs t, hs' t]; simp
    · obtain ⟨v, a, b, c⟩ := hv e
      obtain ⟨v', a', b', c'⟩ := hv' e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      refine ⟨v, a, b, ?_⟩
      rw [valAt_add', c, c']
      refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  · refine ⟨s * s', fun t => ?_, fun e => ?_⟩
    · rw [valAt_mul', hs t, hs' t]; simp
    · obtain ⟨v, a, b, c⟩ := hv e
      obtain ⟨v', a', b', c'⟩ := hv' e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      refine ⟨v, a, b, ?_⟩
      rw [valAt_mul', c, c']
      refine TrivSqZeroExt.ext ?_ ?_
      · simp
      · simp [TrivSqZeroExt.snd_mul, mul_comm, add_comm]

theorem der_unique [Finite T] [Module.Projective R L]
    (hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v')
    {f : T → R} {w w' : Module.Dual R L} (hf : Der Γ N i M f w) :
    Der Γ N i M f w' ↔ ∃ u : Module.Dual R L, w' = w + N • u := by
  obtain ⟨s, hs, hv⟩ := hf
  constructor
  · rintro ⟨s', hs', hv'⟩
    have hss : s' = s := by
      refine sub_eq_zero.mp (_root_.GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic R T Γ ⊤ (s' - s) ?_)
      intro t h
      rw [ValEmb.valAt_sub]
      exact sub_eq_zero.mpr ((hs' t).trans (hs t).symm)
    subst hss
    have hd : ∀ e, Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w' - w) e) = 0 := by
      intro e
      obtain ⟨v, a, b, c⟩ := hv e
      obtain ⟨v', a', b', c'⟩ := hv' e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      have h3 := c'.symm.trans c
      have h4 : Ideal.Quotient.mk (Ideal.span {(N : R)}) (w' e) =
          Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) := by
        simpa using congrArg TrivSqZeroExt.snd h3
      rw [LinearMap.sub_apply, map_sub, h4, sub_self]
    obtain ⟨u, hu'⟩ := dual_eq_smul N (w' - w) hd
    exact ⟨u, by rw [← hu']; abel⟩
  · rintro ⟨u, rfl⟩
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, a, b, c⟩ := hv e
    refine ⟨v, a, b, ?_⟩
    rw [c]
    have h0 : Ideal.Quotient.mk (Ideal.span {(N : R)}) ((w + N • u) e) =
        Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) := by
      refine Ideal.Quotient.eq.mpr ?_
      rw [Ideal.mem_span_singleton]
      exact ⟨u e, by simp⟩
    rw [h0]

end Der

end GlobalTheory.CompanionTheory.Ar.HT.TwDer

namespace GlobalTheory.CompanionTheory.Ar.HT.TwDer

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tan GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem der_all {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}
    {i : Γ.G.left ⟶ G.left} (ht : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L]
    [Module.Projective R L] (M : LieModel G x L) {j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))}
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (U : Γ.G.left.Opens) (hU : ∀ z, η[Γ.G].left z ∈ U) [IsOpenImmersion (U.ι ≫ j)] :
    (∀ f ∈ Γ.btOrder ⊤, ∃ w, Der Γ N i M f w) ∧
    (∀ f w w', Der Γ N i M f w → (Der Γ N i M f w' ↔ ∃ u : Module.Dual R L, w' = w + N • u)) ∧
    (∀ w, ∃ f ∈ Γ.btOrder ⊤, Der Γ N i M f w) ∧
    (∀ f g w w', Der Γ N i M f w → Der Γ N i M g w' →
      Der Γ N i M (f + g) (w + w') ∧ Der Γ N i M (f * g) (f 1 • w' + g 1 • w)) ∧
    (∀ r : R, Der Γ N i M (fun _ => r) 0) ∧
    ∀ f : augIdeal (Γ.btOrder ⊤), Der Γ N i M f.1.1 0 → (f : Γ.btOrder ⊤) ∈ augIdeal (Γ.btOrder ⊤) ^ 2 := by
  have hex : ∀ e : L, ∃ v, IsTanPt Γ N i M e v := fun e =>
    (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).exists
  have hu : ∀ (e : L) (v v'), IsTanPt Γ N i M e v → IsTanPt Γ N i M e v' → v = v' := fun e _ _ h h' =>
    (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).unique h h'
  obtain ⟨θ, hsurj, -, hpin⟩ := omega_open Γ ht M hj U hU
  have hsec : ∀ f : Γ.btOrder ⊤, ∃ s, Γ.HasValues s (f : T → R) := fun f =>
    ⟨j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f), fun t =>
      ValEmb.valAt_pull j (Γ.pt t).left _ (hj.pt t) f⟩
  have hpinD : ∀ (g : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L),
      θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent g → Der Γ N i M g.1.1 w := by
    intro g w h
    obtain ⟨s, hs⟩ := hsec g.1
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, a, b⟩ := hex e
    refine ⟨v, a, b, ?_⟩
    have h0 : (g.1.1 : T → R) 1 = 0 := g.2
    rw [(hpin g w s hs).1 h e v a b, h0]
    simp
  refine ⟨fun f hf => ?_, fun f w w' h => der_unique hu h, fun w => ?_, fun f g w w' h h' => der_add_mul hu h h',
    fun r => der_const Γ N i M r hex, fun f h => ?_⟩
  · let a : Γ.btOrder ⊤ := ⟨f, hf⟩
    let g : augIdeal (Γ.btOrder ⊤) := ⟨a - algebraMap R _ (f 1), by
      rw [OrderApi.mem_augIdeal]
      simp [a]⟩
    obtain ⟨w, hw⟩ := hsurj ((augIdeal (Γ.btOrder ⊤)).toCotangent g)
    have h1 := (der_add_mul hu (hpinD g w hw) (der_const Γ N i M (f 1) hex)).1
    refine ⟨w + 0, ?_⟩
    convert h1 using 1
    ext t
    simp [g, a]
  · obtain ⟨g, hg⟩ := Ideal.toCotangent_surjective _ (θ w)
    exact ⟨g.1.1, g.1.2, hpinD g w hg.symm⟩
  · obtain ⟨s, hs, hv⟩ := h
    have h0 : (f.1.1 : T → R) 1 = 0 := f.2
    have h1 := (hpin f 0 s hs).2 (fun e v a b => by
      obtain ⟨v', a', b', c'⟩ := hv e
      obtain rfl := hu e v v' ⟨a, b⟩ ⟨a', b'⟩
      rw [c', h0]
      simp)
    rw [map_zero] at h1
    exact (Ideal.toCotangent_eq_zero _ _).1 h1.symm

theorem finite_levGrp' {La : Type} [AddCommGroup La] [Module.Finite ℤ La] {p : ℕ} (hp : p.Prime) (n : ℕ) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun t => ?_
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (pow_pos hp.pos n).ne')⟩, ?_⟩
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨b, by rw [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  infer_instance

theorem valuationRing_of_integers {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [IsDomain O]
    [Algebra O C] (hv : v.Integers O) : ValuationRing O := by
  haveI : PreValuationRing O := by
    refine ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_of_le h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_of_le h
      exact ⟨c, Or.inl hc.symm⟩
  exact {}

theorem der_main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L) (n : ℕ), (∀ f ∈ (X.Γ n).btOrder ⊤, ∃ w, X.IsDer M n f w) ∧ (∀ f w w', X.IsDer M n f w → (X.IsDer M n f w' ↔ ∃ u : Module.Dual O L, w' = w + (p ^ n) • u)) ∧ (∀ w, ∃ f ∈ (X.Γ n).btOrder ⊤, X.IsDer M n f w) ∧ (∀ f g w w', X.IsDer M n f w → X.IsDer M n g w' → X.IsDer M n (f + g) (w + w') ∧ X.IsDer M n (f * g) (f 1 • w' + g 1 • w)) ∧ (∀ r : O, X.IsDer M n (fun _ => r) 0) ∧ ∀ f : augIdeal ((X.Γ n).btOrder ⊤), X.IsDer M n f.1.1 0 → (f : (X.Γ n).btOrder ⊤) ∈ augIdeal ((X.Γ n).btOrder ⊤) ^ 2 := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO S _ G _ _ hG y La _ _ _ X L _ _ M n
  haveI : ValuationRing O := valuationRing_of_integers v hv
  haveI : IsLocalRing O := inferInstance
  haveI : IsIntegrallyClosed O := inferInstance
  haveI : Smooth G.hom := hG.smooth
  haveI : Finite (LevGrp La p n) := finite_levGrp' (Fact.out) n
  haveI : Module.Projective O L := (_root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange S G O y L M).2.1
  obtain ⟨U, H, hfin, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.tw_hopf_main p C v O hv hp hO S G hG y La X
  have hex : ∃ j : (X.Γ n).G.left ⟶ Spec (CommRingCat.of ((X.Γ n).btOrder ⊤)),
      (X.Γ n).IsEmb ((X.Γ n).btOrder ⊤) j := by
    let Γ := X.Γ n
    let A := Γ.btOrder ⊤
    have htop (t : LevGrp La p n) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (s : Γ(Γ.G.left, ⊤)) :
        valAt (Γ.pt t).left ⊤ h s = PositivityTheory.HtPt.Mh.val (Γ.pt t).left s := by
      simp only [valAt, PositivityTheory.HtPt.Mh.val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have hsec (a : A) : ∃ s : Γ(Γ.G.left, ⊤), ∀ t,
        PositivityTheory.HtPt.Mh.val (Γ.pt t).left s = algebraMap O (FractionRing O) (a.1 t) := by
      have ha := (PositivityTheory.HtPt.Twhopf.mem_order O _ Γ ⊤ a.1).1 a.2
      obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Twhopf.reg_iff O _ Γ ⊤ _).1 (ha 1)
      refine ⟨s, fun t => (htop t le_top s).symm.trans ?_⟩
      simpa only [_root_.one_mul] using hs t le_top
    have hsec_ext {s s' : Γ(Γ.G.left, ⊤)}
        (h : ∀ t, PositivityTheory.HtPt.Mh.val (Γ.pt t).left s = PositivityTheory.HtPt.Mh.val (Γ.pt t).left s') : s = s' := by
      rw [← sub_eq_zero]
      refine _root_.GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic O _ Γ ⊤ _ fun t ht => ?_
      rw [htop, map_sub, h, sub_self]
    have hhom_ext {B : Type} [CommRing B] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of B)}
        (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
      PositivityTheory.HtPt.Mh.pb_ext fun a => hsec_ext fun t => by
        rw [PositivityTheory.HtPt.Mh.val_pb_comp, h, ← PositivityTheory.HtPt.Mh.val_pb_comp]
    choose s hs using hsec
    let φ : A →+* Γ(Γ.G.left, ⊤) :=
      { toFun := s
        map_one' := hsec_ext fun t => by rw [hs, map_one]; simp
        map_mul' := fun a b => hsec_ext fun t => by rw [hs, map_mul, hs, hs]; simp
        map_zero' := hsec_ext fun t => by rw [hs, map_zero]; simp
        map_add' := fun a b => hsec_ext fun t => by rw [hs, map_add (f := _), hs, hs]; simp }
    obtain ⟨j, hj⟩ := PositivityTheory.HtPt.Mh.exists_pb φ
    have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
        ((algebraMap O (FractionRing O)).comp
          ((Pi.evalRingHom (fun _ : LevGrp La p n => O) t).comp A.val.toRingHom))) := by
      intro t
      apply PositivityTheory.HtPt.Mh.comp_eq_spec
      intro a
      rw [hj]
      exact hs a t
    refine ⟨j, ⟨?_, hpt⟩⟩
    apply hhom_ext
    intro t
    rw [← Category.assoc, hpt, PositivityTheory.HtPt.Mh.spec_comp, Over.w (Γ.pt t)]
    show _ = Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))
    congr 2
  obtain ⟨j, hj⟩ := hex
  haveI := (GlobalTheory.CompanionTheory.Ar.BT.EmbSub.openImmersion_translatesCover O _ (X.Γ n) (U n) (hfin n) j hj).1
  exact der_all (X.Γ n) (X.tors n) M hj (U n) (hfin n).one

end GlobalTheory.CompanionTheory.Ar.HT.TwDer
