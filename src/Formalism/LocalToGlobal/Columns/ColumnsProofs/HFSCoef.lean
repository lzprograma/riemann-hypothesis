module

import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSLin
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Formalism.LocalRingCardinality.Params

@[expose] public section

open Module NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

section VVMap

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {σ : Type} [Fintype σ] {n : ℕ} (lam : σ → DomWeight n)

theorem hfs_map_mem_VV {F : Pol K σ n} (hF : F ∈ VV K lam) : MvPolynomial.map ι F ∈ VV L lam := by
  apply _root_.Formalism.L2.Ker.map_mem_VV <;> assumption

def hfsJ : VV K lam →+ VV L lam where
  toFun v := ⟨MvPolynomial.map ι (v : Pol K σ n), hfs_map_mem_VV ι lam v.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' v w := Subtype.ext (map_add _ _ _)

theorem hfsJ_coe (v : VV K lam) : ((hfsJ ι lam v : VV L lam) : Pol L σ n) = MvPolynomial.map ι (v : Pol K σ n) := rfl

theorem hfsJ_smul (a : K) (v : VV K lam) : hfsJ ι lam (a • v) = ι a • hfsJ ι lam v := by
  apply Subtype.ext
  rw [hfsJ_coe, Submodule.coe_smul, Submodule.coe_smul, hfsJ_coe, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem hfsJ_li (F : CoefFrame ι) : LinearIndependent L fun i => hfsJ ι lam (bVV K lam i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hpol : ∑ j ∈ s, g j • MvPolynomial.map ι ((bVV K lam j : VV K lam) : Pol K σ n) = 0 := by
    have h0 := congrArg (fun v : VV L lam => (v : Pol L σ n)) hg
    simpa [hfsJ_coe] using h0
  have hK : ∀ k, ∑ j ∈ s, F.c (g j) k • ((bVV K lam j : VV K lam) : Pol K σ n) = 0 := by
    intro k
    ext d
    have h1 := congrArg (AddMonoidAlgebra.coeff · d) hpol
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1 ⊢
    have h2 := congrArg (fun y => F.c y k) h1

    simp only [map_sum, map_zero, Finset.sum_apply, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (g j), F.smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hli := (bVV K lam).linearIndependent
  rw [linearIndependent_iff'] at hli
  have hz : ∀ k, F.c (g i) k = 0 := by
    intro k
    refine hli s (fun j => F.c (g j) k) ?_ i hi
    apply Subtype.ext
    simpa using hK k
  rw [F.spec (g i)]
  simp [hz]

theorem hfsJ_span (F : CoefFrame ι) : ⊤ ≤ Submodule.span L (Set.range fun i => hfsJ ι lam (bVV K lam i)) := by
  classical
  haveI : FiniteDimensional L (VV L lam) := Module.Basis.finiteDimensional_of_finite (bVV L lam)
  rw [(hfsJ_li ι lam F).span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis (bVV L lam)).symm]

end VVMap

section Act

variable {K L : Type} [Field K] [Field L] (ι : K →+* L) {σ : Type} [Fintype σ] {n : ℕ} (lam : σ → DomWeight n)

theorem hfs_map_trAct (g : σ → GL (Fin n) K) (F : Pol K σ n) :
    MvPolynomial.map ι (trAct g F) = trAct (fun τ => Formalism.UG.bc ι (g τ)) (MvPolynomial.map ι F) := by
  unfold trAct Formalism.GradedWeylDivisibility.blockAct
  rw [MvPolynomial.map_aeval_eq_aeval_map ι (MvPolynomial.map ι)
    (by ext x; simp [MvPolynomial.algebraMap_eq])]
  refine congrArg (fun g => MvPolynomial.aeval g _) (funext fun v => ?_)
  simp [map_sum, Formalism.UG.bc, Matrix.transpose_apply]

theorem hfs_detPow_bc (g : GL (Fin n) K) (c : ℤ) : detPow L n (Formalism.UG.bc ι g) c = ι (detPow K n g c) := by
  unfold detPow
  have h : Matrix.GeneralLinearGroup.det (Formalism.UG.bc ι g) =
      Units.map (ι : K →* L) (Matrix.GeneralLinearGroup.det g) := by
    ext
    simp [Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [h, ← map_zpow, Units.coe_map]
  rfl

theorem hfs_detTwK_bc (g : σ → GL (Fin n) K) : detTwK lam (fun τ => Formalism.UG.bc ι (g τ)) = ι (detTwK lam g) := by
  unfold detTwK
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => hfs_detPow_bc ι (g τ) _

theorem hfs_map_actP (g : σ → GL (Fin n) K) (F : Pol K σ n) :
    MvPolynomial.map ι (actP lam g F) = actP lam (fun τ => Formalism.UG.bc ι (g τ)) (MvPolynomial.map ι F) := by
  unfold actP
  rw [LinearMap.smul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hfs_map_trAct,
    hfs_detTwK_bc]

theorem hfs_rhoK (g : σ → GL (Fin n) K) (v : VV K lam) :
    rhoK lam (fun τ => Formalism.UG.bc ι (g τ)) (hfsJ ι lam v) = hfsJ ι lam (rhoK lam g v) := by
  apply Subtype.ext
  show actP lam (fun τ => Formalism.UG.bc ι (g τ)) ((hfsJ ι lam v : VV L lam) : Pol L σ n) =
    MvPolynomial.map ι (actP lam g (v : Pol K σ n))
  rw [hfsJ_coe, hfs_map_actP]

variable [NumberField K] [NumberField L] {E : Type} [Field E] [NumberField E]

theorem hfs_embGL (emb : σ → E →+* K) (γ : GL (Fin n) E) :
    embGL (fun τ => ι.comp (emb τ)) γ = fun τ => Formalism.UG.bc ι (embGL emb γ τ) := by
  funext τ
  apply Units.ext
  ext i j
  simp [embGL, Formalism.UG.bc]

theorem hfs_invTrK (g : σ → GL (Fin n) K) : invTrK (fun τ => Formalism.UG.bc ι (g τ)) = fun τ => Formalism.UG.bc ι (invTrK g τ) := by
  funext τ
  apply Units.ext
  show ((((Formalism.UG.bc ι (g τ))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).transpose =
    ((Formalism.UG.bc ι (inside₂ K n (g τ)) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  rw [← map_inv]
  ext i j
  simp [Formalism.UG.bc, inside₂]

theorem hfs_rhoV (emb : σ → E →+* K) (γ : GL (Fin n) E) (v : VV K lam) :
    rhoV (fun τ => ι.comp (emb τ)) lam γ (hfsJ ι lam v) = hfsJ ι lam (rhoV emb lam γ v) := by
  show DIV.rhoK lam (embGL (fun τ => ι.comp (emb τ)) γ) (hfsJ ι lam v) =
    hfsJ ι lam (DIV.rhoK lam (embGL emb γ) v)
  rw [hfs_embGL]
  exact hfs_rhoK ι lam _ v

theorem hfs_rhoVr (emb : σ → E →+* K) (γ : GL (Fin n) E) (v : VV K lam) :
    rhoVr (fun τ => ι.comp (emb τ)) lam γ (hfsJ ι lam v) = hfsJ ι lam (rhoVr emb lam γ v) := by
  show DIV.rhoK lam (invTrK (embGL (fun τ => ι.comp (emb τ)) γ)) (hfsJ ι lam v) =
    hfsJ ι lam (DIV.rhoK lam (invTrK (embGL emb γ)) v)
  rw [hfs_embGL, hfs_invTrK]
  exact hfs_rhoK ι lam _ v

end Act

end Formalism.L2.Col
