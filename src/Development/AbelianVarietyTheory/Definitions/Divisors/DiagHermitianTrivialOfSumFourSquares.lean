module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarization

@[expose] public section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

variable {p : ℕ} [Fact p.Prime]

structure DPair (G : HTGroup p) where

  β : G.Cˣ

  γ : G.Cˣ

  c : ℚˣ
  sym : sh G β = β
  sim : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β
  reg : (minpoly G.F (γ : G.C)).natDegree = G.n ∧ (minpoly G.F (γ : G.C)).Separable
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t

  posR : ∀ v : InfinitePlace G.F, ∀ x : Fin G.n → ℂ, x ≠ 0 →
    (sigPosH (G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re < 0)

namespace DPair

variable {G : HTGroup p}

def pol (P : DPair G) : Polynomial G.F := minpoly G.F (P.γ : G.C)

def Rel (P Q : DPair G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y) ∧ Q.γ = y * P.γ * y⁻¹

def cent (P : DPair G) : Subgroup (G.Cˣ × ℚˣ) := centOf G P.β P.γ

def self (P : DPair G) : P.cent := ⟨(P.γ, P.c), rfl, P.sim⟩

def toAf (P : DPair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : P.cent →* G.GAf :=
  toAfOf G P.β P.γ x t hx

def atP (P : DPair G) : Gp G := locC G (P.γ, P.c)

def toQr (P : DPair G) (r : ℕ) (z : Gr G r) : P.cent →* Gr G r :=
  ((carry G r z).comp (locC G)).comp P.cent.subtype

def termAt (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r) : ℂ :=
  GlobalTheory.LKCount.pointSum (P.toAf x t hx) (P.toQr r z) (sigG G r) Kf K (P.toAf x t hx P.self) δ f φ

def term (P : DPair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  if h : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 then
    P.termAt Kf f r K φ P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec
      h.choose.1 h.choose.2
  else 0

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_eq_sh_mul_sh_rev (a b : G.C) :
    _root_.GlobalTheory.LKMid.sh G (a * b) =
      _root_.GlobalTheory.LKMid.sh G b * _root_.GlobalTheory.LKMid.sh G a := by
  simp only [_root_.GlobalTheory.LKMid.sh, map_mul, MulOpposite.unop_mul]

open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
private theorem lkMid_sh_mul_sh_units_inv_eq_one (y : (G.C)ˣ) :
    _root_.GlobalTheory.LKMid.sh G y *
      _root_.GlobalTheory.LKMid.sh G ((y⁻¹ : (G.C)ˣ) : G.C) = 1 := by
  rw [← lkMid_sh_mul_eq_sh_mul_sh_rev, Units.inv_mul, _root_.GlobalTheory.LKMid.sh_one_eq]


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.rel_equivalence (G : _root_.GlobalTheory.LKTrip.HTGroup p) :
    Equivalence (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) := by
  refine ⟨fun P => ?_, fun {P₁ P₂} h => ?_, fun {P₁ P₂ P₃} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, by simp⟩
    simp [_root_.GlobalTheory.LKMid.sh_one_eq]
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul]
      simp only [mul_assoc, Units.inv_mul_cancel_left, lkMid_sh_mul_sh_units_inv_eq_one, mul_one]
      rw [mul_inv_cancel₀ hs.ne', one_smul]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, lkMid_sh_mul_eq_sh_mul_sh_rev]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
      rw [mul_comm s s']
    · rw [hγ', hγ]; group

theorem pol_eq_of_rel {P Q : DPair G} (h : P.Rel Q) : Q.pol = P.pol := by
  obtain ⟨y, s, _, _, hγ⟩ := h
  have h := minpoly.algEquiv_eq (Pair.innerAlgEquiv G.F y) (P.γ : G.C)
  simp only [pol, hγ, Units.val_mul]
  exact h


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.mk_eq_iff (P Q : _root_.GlobalTheory.LKDef.DPair G) :
    Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P = Quot.mk _ Q ↔
      P.Rel Q :=
  ⟨fun h => (_root_.GlobalTheory.LKDef.DPair.rel_equivalence G).eqvGen_iff.mp (Quot.eqvGen_exact h),
    Quot.sound⟩


open Matrix NumberField in
open scoped TensorProduct Classical in
variable {p : ℕ} [Fact p.Prime] in
variable {G : _root_.GlobalTheory.LKTrip.HTGroup p} in
theorem _root_.GlobalTheory.LKDef.DPair.rel_out (P : _root_.GlobalTheory.LKDef.DPair G) :
    P.Rel
      (Quot.out (Quot.mk (_root_.GlobalTheory.LKDef.DPair.Rel (G := G)) P)) :=
  (_root_.GlobalTheory.LKDef.DPair.mk_eq_iff P _).mp (Quot.out_eq _).symm

end DPair

def DCls (G : HTGroup p) : Type := Quot (DPair.Rel (G := G))

def dSumIrr (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : DCls G, if Irreducible (Quot.out q).pol then wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

namespace Example

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example

end Example

end GlobalTheory.LKDef
