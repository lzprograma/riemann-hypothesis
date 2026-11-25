module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealFrameCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.MatEqZeroOfSpan

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.RootCoordinatesIndex

theorem hpk_eI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) (Formalism.QuantumDeterminants.eI k r a) = v (Formalism.QuantumDeterminants.esI k r a) := by
  apply _root_.PI.AmpRootHaarW.Hpk_mulVec_eI <;> assumption

section Gen

variable {D : D7} {X : HidaSetting D} (v : InfinitePlace X.B.I.F) {lam : ℂ}
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
  {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}

theorem Q_e_of (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (a : Fin D.R.rS) :
    Q *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 = lam ^ (D.R.rS - a.val) • rv X.B.I v (X.eR a) :=
  (hT.2.2.2 a a rfl).1

theorem Qi_e_of (hl : lam ≠ 0) (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (a : Fin D.R.rS) :
    Qi *ᵥ rv X.B.I v (X.eR a) = (lam ^ (D.R.rS - a.val))⁻¹ • Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 := by
  have h := congrArg (fun x => Qi *ᵥ x) (Q_e_of v hT a)
  simp only [Matrix.mulVec_mulVec, hT.1, Matrix.one_mulVec, Matrix.mulVec_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]

theorem Qi_spanLt_of (hl : lam ≠ 0) (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    (a : ℕ) (x : Fin X.B.I.n → ℂ) (hx : x ∈ spanLt (fun b : Fin D.R.rS => rv X.B.I v (X.eR b)) a)
    (i : Fin (2 * D.R.rS + D.R.k + 1)) (hi : a ≤ i.val) : (Qi *ᵥ x) i = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨b, hb, rfl⟩ := hx'
    rw [Qi_e_of v hl hT, Pi.smul_apply, Pi.single_apply, ite_eq_right, smul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [Formalism.QuantumDeterminants.eI] at this
    simp only [Set.mem_setOf_eq] at hb
    omega
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]

theorem Q_spanLt_of (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    (a : ℕ) (ha : a ≤ D.R.rS) (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → w i = 0) :
    Q *ᵥ w ∈ spanLt (fun b : Fin D.R.rS => rv X.B.I v (X.eR b)) a := by
  have hw' : w = ∑ i, w i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw', Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : a ≤ i.val
  · rw [hw i hi, zero_smul, Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  · have hir : i.val < D.R.rS := by omega
    have e : i = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨i.val, hir⟩ := Fin.ext rfl
    rw [Matrix.mulVec_smul, e, Q_e_of v hT]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.val, hir⟩, ?_, rfl⟩))
    simp only [Set.mem_setOf_eq]
    omega

theorem hJ_e_of (hl : lam ≠ 0) (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (a : Fin D.R.rS) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) y = star ((lam ^ (D.R.rS - a.val))⁻¹) * (Qi *ᵥ y) (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨_, hQQi, hH, _⟩ := hT
  have he : rv X.B.I v (X.eR a) = (lam ^ (D.R.rS - a.val))⁻¹ • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1) := by
    rw [Q_e_of v ⟨‹_›, hQQi, hH, ‹_›⟩, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]
  have hy : y = Q *ᵥ (Qi *ᵥ y) := by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  conv_lhs => rw [he, hy]
  unfold hJ
  rw [star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH,
    Pi.star_single, star_one, single_dotProduct, one_mul, hpk_eI, smul_eq_mul]

theorem inN_iff_of (hl : lam ≠ 0) (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    (z : Fin X.B.I.n → ℂ) (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (Qi *ᵥ z))
    (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε v) * g = Formalism.REAL.Jm (X.B.I.ε v)) :
    InN (X.B.I.ε v) (fun b : Fin D.R.rS => rv X.B.I v (X.eR b)) z g ↔ Qi * g * Q ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  have hQiQ := hT.1
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  have hstar_ne : ∀ a : Fin D.R.rS, star ((lam ^ (D.R.rS - a.val))⁻¹) ≠ 0 := fun a =>
    star_ne_zero.2 (inv_ne_zero (pow_ne_zero _ hl))
  have hcol : ∀ (M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) i j,
      M i j = (M *ᵥ Pi.single j 1) i := fun M i j => by rw [Matrix.mulVec_single_one]; rfl
  constructor
  · rintro ⟨⟨hIe, hIz⟩, hperp⟩
    refine ⟨?_, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩
    · show (Qi * g * Q)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Qi * g * Q) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
      have hQiQ' : Qiᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one]
      rw [← hH]
      calc (Qi * g * Q)ᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * (Qi * g * Q)
          = Qᴴ * (gᴴ * (Qiᴴ * Qᴴ) * Formalism.REAL.Jm (X.B.I.ε v) * ((Q * Qi) * g)) * Q := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQiQ', hQQi, Matrix.mul_one, Matrix.one_mul, hg]
    · rw [hcol (Qi * g * Q) i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a)]
      have h1 : (Qi * g * Q) *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 =
          Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 +
            lam ^ (D.R.rS - a.val) • (Qi *ᵥ ((g - 1) *ᵥ rv X.B.I v (X.eR a))) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Q_e_of v hT, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Qi_e_of v hl hT, smul_sub, smul_smul,
          mul_inv_cancel₀ (pow_ne_zero _ hl), one_smul]
        abel
      rw [h1, Pi.add_apply, Pi.smul_apply, Qi_spanLt_of v hl hT a.val _ (hIe a) i hai, smul_zero, add_zero, Pi.single_apply]
    · rw [hcol (Qi * g * Q) i j]
      have horth : ∀ b : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.eR b)) (Q *ᵥ Pi.single j 1) = 0 := by
        intro b
        rw [hJ_e_of v hl hT, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Pi.single_apply, ite_eq_right, mul_zero]
        intro h
        have := congrArg Fin.val h
        simp only [Formalism.QuantumDeterminants.esI] at this
        have := b.isLt
        omega
      have h1 : (Qi * g * Q) *ᵥ Pi.single j 1 =
          Pi.single j 1 + Qi *ᵥ ((g - 1) *ᵥ (Q *ᵥ Pi.single j 1)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
        simp only [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Matrix.mul_assoc]
        abel
      rw [h1, Pi.add_apply, Qi_spanLt_of v hl hT D.R.rS _ (hperp _ horth) i hi, add_zero, Pi.single_apply]
  · rintro ⟨_, hce, hcw⟩
    have hg' : g = Q * (Qi * g * Q) * Qi := by
      simp only [← Matrix.mul_assoc]
      rw [hQQi, Matrix.one_mul, Matrix.mul_assoc, hQQi, Matrix.mul_one]
    set m := Qi * g * Q with hm
    have key : ∀ x, (g - 1) *ᵥ x = Q *ᵥ ((m - 1) *ᵥ (Qi *ᵥ x)) := by
      intro x
      conv_lhs => rw [hg']
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    have hmW : ∀ x : Fin (2 * D.R.rS + D.R.k + 1) → ℂ, (∀ a, x (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0) →
        ∀ i : Fin (2 * D.R.rS + D.R.k + 1), D.R.rS ≤ i.val → ((m - 1) *ᵥ x) i = 0 := by
      intro x hx i hi
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj1 : j.val < D.R.rS
      · have e : j = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨j.val, hj1⟩ := Fin.ext rfl
        have := hce ⟨j.val, hj1⟩ i (by simp only; omega)
        rw [Matrix.sub_apply, e, this, Matrix.one_apply, sub_self, zero_mul]
      · by_cases hj2 : j.val ≤ D.R.rS + D.R.k
        · rw [Matrix.sub_apply, hcw i j (by omega) hj2 hi, Matrix.one_apply, sub_self, zero_mul]
        · have hjr : 2 * D.R.rS + D.R.k - j.val < D.R.rS := by have := j.isLt; omega
          have e : j = Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨2 * D.R.rS + D.R.k - j.val, hjr⟩ := by
            ext; simp only [Formalism.QuantumDeterminants.esI]; have := j.isLt; omega
          rw [e, hx, mul_zero]
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · rw [key, Qi_e_of v hl hT, Matrix.mulVec_smul, Matrix.mulVec_smul]
      refine Submodule.smul_mem _ _ (Q_spanLt_of v hT a.val a.isLt.le _ fun i hi => ?_)
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hcol m i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a), hce a i hi,
        Pi.single_apply, sub_self]
    · rw [key]
      refine Q_spanLt_of v hT D.R.rS le_rfl _ (hmW _ (fun a => hz _ (Or.inr ?_)))
      simp only [Formalism.QuantumDeterminants.esI]
      have := a.isLt
      omega
    · rw [key]
      refine Q_spanLt_of v hT D.R.rS le_rfl _ (hmW _ fun a => ?_)
      have h1 := hy a
      rw [hJ_e_of v hl hT] at h1
      exact (mul_eq_zero.1 h1).resolve_left (hstar_ne a)

end Gen

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau)

abbrev eV (a : Fin D.R.rS) : Fin X.B.I.n → ℂ := rv X.B.I (vOf X τ) (X.eR a)

theorem Q_e (a : Fin D.R.rS) :
    C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 = frS D ^ (D.R.rS - a.val) • eV τ a :=
  Q_e_of (vOf X τ) (C.isT τ) a

theorem Qi_e (a : Fin D.R.rS) :
    C.Qi τ *ᵥ eV τ a = (frS D ^ (D.R.rS - a.val))⁻¹ • Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 :=
  Qi_e_of (vOf X τ) (_root_.Formalism.L2.SG.Pf.Choice.frS_ne D) (C.isT τ) a

theorem Qi_spanLt (a : ℕ) (x : Fin X.B.I.n → ℂ) (hx : x ∈ spanLt (eV (X := X) τ) a) (i : Fin (2 * D.R.rS + D.R.k + 1))
    (hi : a ≤ i.val) : (C.Qi τ *ᵥ x) i = 0 :=
  Qi_spanLt_of (vOf X τ) (_root_.Formalism.L2.SG.Pf.Choice.frS_ne D) (C.isT τ) a x hx i hi

theorem Q_spanLt (a : ℕ) (ha : a ≤ D.R.rS) (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → w i = 0) : C.Q τ *ᵥ w ∈ spanLt (eV (X := X) τ) a :=
  Q_spanLt_of (vOf X τ) (C.isT τ) a ha w hw

theorem hJ_e (a : Fin D.R.rS) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε (vOf X τ)) (eV τ a) y = star ((frS D ^ (D.R.rS - a.val))⁻¹) * (C.Qi τ *ᵥ y) (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) :=
  hJ_e_of (vOf X τ) (_root_.Formalism.L2.SG.Pf.Choice.frS_ne D) (C.isT τ) a y

variable {C τ}

theorem inN_iff (z : Fin X.B.I.n → ℂ) (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (C.Qi τ *ᵥ z))
    (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) :
    InN (X.B.I.ε (vOf X τ)) (eV τ) z g ↔ C.Qi τ * g * C.Q τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS :=
  inN_iff_of (vOf X τ) (_root_.Formalism.L2.SG.Pf.Choice.frS_ne D) (C.isT τ) z hz g hg

end Formalism.L2.SG.RootCoordinatesIndex

end
