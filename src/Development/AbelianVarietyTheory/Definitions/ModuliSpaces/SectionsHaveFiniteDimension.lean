module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}

def SectionsHaveFiniteDimension (p : X ⟶ Sp K) (M : LB X) (r : ℕ) : Prop :=
  ∃ s : Fin r → M.Sec, ∀ t : M.Sec, ∃! a : Fin r → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j

def Vol (p : X ⟶ Sp K) (M : LB X) (g : ℕ) (δ : ℝ) : Prop :=
  ∃ h : ℕ → ℕ, (∀ e, SectionsHaveFiniteDimension p (lbPow M e) (h e)) ∧
    Filter.Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) Filter.atTop (nhds δ)

def VAmp (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) : Prop :=
  (⨆ i, Out.nonzeroLocus (th i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (th i)) ∧
    ∃ r : σ → Γ(X, Out.nonzeroLocus (th i)),
      (∀ j k, resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG X (inf_le_left : Out.nonzeroLocus (th i) ⊓ M.U k ≤ Out.nonzeroLocus (th i)) (r j) *
          resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th i).f k)) ∧
      ∀ f : Γ(X, Out.nonzeroLocus (th i)), ∃ F : MvPolynomial σ K,
        f = MvPolynomial.eval₂ (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F

def MapDeg (ψ : X ⟶ Y) (D : ℕ) : Prop :=
  ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
    letI := (ψ.app U).hom.toAlgebra
    Module.rank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = (D : Cardinal)

def TorsBasis (A : Over (Sp K)) [GrpObj A] (k : ℕ) {m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) : Prop :=
  0 < k ∧ (∀ i, pt i ^ k = 1) ∧ ∀ y : Out.baseOver (Sp K) ⟶ A, y ^ k = 1 →
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y

def ActsBy {A : Over (Sp K)} [GrpObj A] {k m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) (f : A ⟶ A)
    (Mat : Matrix (Fin m) (Fin m) (ZMod k)) : Prop :=
  0 < k ∧ ∀ i, pt i ≫ f = Out.linComb pt (fun i' => (Mat i' i).val)

def FormIs (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A) : Prop :=
  IsMonHom s ∧ LBIso (abelian₂ P.A M) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ s] P.L)

def SymB {A : Over (Sp K)} [GrpObj A] (M : LB A.left) : Prop := LBIso M (M.pull (GrpObj.inv : A ⟶ A).left)

theorem vAmp_iff_veryAmpleBy (p : X ⟶ Sp K) (M : LB X) {m : ℕ} (s : Fin (m + 1) → M.Sec) :
    VAmp p M s ↔ AbLaw.VeryAmpleBy p M s :=
  and_congr Iff.rfl (forall_congr' fun _ => and_congr Iff.rfl (exists_congr fun _ =>
    and_congr Iff.rfl (forall_congr' fun _ => exists_congr fun _ => eq_comm)))

theorem VAmp.comp_surjective {p : X ⟶ Sp K} {M : LB X} {σ τ : Type} {th : σ → M.Sec} (h : VAmp p M th)
    {e : τ → σ} (he : Function.Surjective e) : VAmp p M (fun i => th (e i)) := by
  refine ⟨(he.iSup_comp fun i => Out.nonzeroLocus (th i)).trans h.1, fun i => ⟨(h.2 (e i)).1, ?_⟩⟩
  obtain ⟨r, hr, hF⟩ := (h.2 (e i)).2
  refine ⟨fun j => r (e j), fun j k => hr (e j) k, fun f => ?_⟩
  obtain ⟨F, rfl⟩ := hF f
  obtain ⟨G, rfl⟩ := MvPolynomial.rename_surjective e he F
  exact ⟨G, MvPolynomial.eval₂_rename _ _ _ _⟩

theorem vAmp_comp_equiv (p : X ⟶ Sp K) (M : LB X) {σ τ : Type} (th : σ → M.Sec) (e : τ ≃ σ) :
    VAmp p M (fun i => th (e i)) ↔ VAmp p M th :=
  ⟨fun h => by simpa only [Equiv.apply_symm_apply] using h.comp_surjective e.symm.surjective,
    fun h => h.comp_surjective e.surjective⟩

theorem vAmp_iff_veryAmpleBy_equiv (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) {m : ℕ}
    (e : Fin (m + 1) ≃ σ) : VAmp p M th ↔ AbLaw.VeryAmpleBy p M (fun i => th (e i)) :=
  (vAmp_comp_equiv p M th e).symm.trans (vAmp_iff_veryAmpleBy p M _)

theorem VAmp.exists_veryAmpleBy {p : X ⟶ Sp K} {M : LB X} {σ : Type} [Finite σ] [Nonempty σ] {th : σ → M.Sec}
    (h : VAmp p M th) : ∃ (m : ℕ) (e : Fin (m + 1) ≃ σ), AbLaw.VeryAmpleBy p M (fun i => th (e i)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun hn => (hn ▸ e (Classical.arbitrary σ) : Fin 0).elim0
  exact ⟨m, e.symm, (vAmp_iff_veryAmpleBy_equiv p M th e.symm).1 h⟩

theorem MapDeg.finrank_eq {ψ : X ⟶ Y} {D : ℕ} (h : MapDeg ψ D) (U : Y.Opens) (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (ψ.app U).hom.toAlgebra
    Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D :=
  (congrArg Cardinal.toNat (h U hU hne)).trans (Cardinal.toNat_natCast D)

theorem MapDeg.of_isFinite {ψ : X ⟶ Y} [IsFinite ψ] {D : ℕ}
    (h : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      letI := (ψ.app U).hom.toAlgebra
      Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D) : MapDeg ψ D := fun U hU hne => by
  letI := (ψ.app U).hom.toAlgebra
  haveI : Nonempty U := hne.to_subtype
  haveI : Module.Finite Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
  exact (Module.finrank_eq_rank _ _).symm.trans (congrArg _ (h U hU hne))

theorem MapDeg.id_one (X : Scheme.{0}) : MapDeg (𝟙 X) 1 := fun U _ hne =>
  haveI : Nonempty U := hne.to_subtype
  (Module.rank_self Γ(X, U)).trans Nat.cast_one.symm

section Torsion
variable {A : Over (Sp K)} [GrpObj A] {k m : ℕ} {pt : Fin m → (Out.baseOver (Sp K) ⟶ A)}

theorem TorsBasis.pos (h : TorsBasis A k pt) : 0 < k := h.1

theorem TorsBasis.pow_eq_one (h : TorsBasis A k pt) (i : Fin m) : pt i ^ k = 1 := h.2.1 i

theorem TorsBasis.existsUnique (h : TorsBasis A k pt) {y : Out.baseOver (Sp K) ⟶ A} (hy : y ^ k = 1) :
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y := h.2.2 y hy

theorem ActsBy.comp_eq {f : A ⟶ A} {Mat : Matrix (Fin m) (Fin m) (ZMod k)} (h : ActsBy pt f Mat) (i : Fin m) :
    pt i ≫ f = Out.linComb pt (fun i' => (Mat i' i).val) := h.2 i

end Torsion

theorem FormIs.isMonHom {P : Out.PolAV (Sp K)} {M : LB P.A.left} {s : P.A ⟶ P.A} (h : FormIs P M s) :
    IsMonHom s := h.1

end GlobalTheory.ZV
end
