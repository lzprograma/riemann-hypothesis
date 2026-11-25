module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiIsEven
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensCub

def tensP {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} (T : Tens D D' W)
    (k : (Fin r × Fin r) × Fin 4) : D'.P.A ⟶ D.P.A :=
  ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2

theorem tensorMap_left {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : (tensP T k).left = tensφ T.pr k := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m <;> rfl

theorem isMonHom_tensorMap {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : IsMonHom (tensP T k) := by
  letI := D.P.isAb.comm
  have := T.pr_hom k.1.1
  have := T.pr_hom k.1.2
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m
  · exact GlobalTheory.Serre.isMonHom_mul _ _
  · exact T.pr_hom i
  · exact T.pr_hom j
  · exact GlobalTheory.Serre.isMonHom_one

theorem cubV_tens : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (S : Over (Spec (CommRingCat.of R))) (z : S.left) (J : (S.left ⟶ D.P.A.left) → D.P.L.ι) (J' : (S.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ x x' y : S ⟶ D'.P.A, (let om := fun p : S ⟶ D'.P.A => gm p.left z _ (T.w.s (fun k => J (p.left ≫ tensφ T.pr k), J' p.left)); cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ k : (Fin r × Fin r) × Fin 4, cubV D.cub z J (x ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (x' ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (y ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) ^ tensε W k) := by
  intro hG R _ _ D D' r W T S z J J' hJ hJ' x x' y om
  let P := tensP T
  let ρ : (Fin r × Fin r) × Fin 4 → ((G3 D'.P.A).left ⟶ (G3 D.P.A).left) := fun k => (P k ⊗ₘ P k ⊗ₘ P k).left
  have hψ : ∀ k a, thφ D'.P.A (x3 D'.P.A) a ≫ tensφ T.pr k = ρ k ≫ thφ D.P.A (x3 D.P.A) a := fun k a => by
    rw [← tensorMap_left T k]
    letI := isMonHom_tensorMap T k
    exact (CubeMap.ofHom (P k)).psum_comm a.down
  have hρ : ∀ {T : Over (Spec (CommRingCat.of R))} (a b c : T ⟶ D'.P.A) k, (lift a (lift b c)).left ≫ ρ k =
      (lift (a ≫ P k) (lift (b ≫ P k) (c ≫ P k))).left := fun a b c k => by
    show (lift a (lift b c) ≫ (P k ⊗ₘ P k ⊗ₘ P k)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := GlobalTheory.TensEven.box_uniqueE (pr := tensφ T.pr) (εp := tensε W) D.P.isLB D'.P.isLB T.w T.w_gen (ε := thε) hψ
    D'.cub.isGen D.cub.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV D'.cub s I') := isCub_cubV D'.cub hI'
      have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I) := isCub_cubV D.cub hI
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
        (fun q => GlobalTheory.TensEven.bwE T.w q s (fun i => I (q ≫ tensφ T.pr i)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun k _ => ?_).symm)
      have := isMonHom_tensorMap T k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ P k = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ k = _ from hρ 1 1 1 k, o]
      exact (congrArg (· ^ tensε W k) (C.face 1 1)).trans (one_zpow _)) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => GlobalTheory.TensEven.bwE T.w q z (fun i => J (q ≫ tensφ T.pr i)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun k _ => ?_)))
  rw [hρ]; rfl

end GlobalTheory.TensCub
