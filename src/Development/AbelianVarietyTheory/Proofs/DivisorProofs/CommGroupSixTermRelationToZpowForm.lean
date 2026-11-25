module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AdjPolLocal
open GlobalTheory.MulPull GlobalTheory.PrimNorm GlobalTheory.PrimNormPol

theorem le_val_one_add_pow_sub {G : Type} [CommGroup G] {D a b : G} (h : 1 = D * (1 * a⁻¹ * b⁻¹ * 1)) : D = a * b := by
  rw [_root_.one_mul, _root_.mul_one, eq_comm, ← mul_inv, mul_inv_eq_one] at h
  exact h

theorem lbIso_of_rosatiAdj_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (f g : B ⟶ B), M.IsLB → RosatiAdj B M f g → LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) := by
  intro R _ _ B _ _ M f g hM h
  obtain ⟨U, hU, t, ht⟩ := h (closedPoint R)
  have hall : ∀ p : Sp R, p ∈ U := fun p =>
    Specializes.mem_open ((PrimeSpectrum.le_iff_specializes p (closedPoint R)).1
      (le_maximalIdeal p.2.ne_top)) U.isOpen hU
  have H : KerPow.HasGen M (rosatiφ B f g) rosatiε :=
    KerPow.HasGen.of_range (W := (B ⊗ B).hom ⁻¹ᵁ U) ⟨t, ht⟩ (𝟙 _) (fun y => hall _) (fun k => Category.id_comp _)
  let φ := fun I : ULift (Finset (Fin 2)) => (psum B ![fst B B ≫ f, snd B B] I.down).left
  let ψ := fun I : ULift (Finset (Fin 2)) => (psum B ![fst B B, snd B B ≫ g] I.down).left
  let ε := fun I : ULift (Finset (Fin 2)) => (-1 : ℤ) ^ (2 - I.down.card)
  have hh' : MulPull.HasGen M (Sum.elim ψ φ) (Sum.elim ε fun i => -ε i) := by
    refine (MulPull.HasGen.inv H).of_formEq hM (fun U _ q => ?_)
    rw [Fin.prod_univ_six, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    dsimp [φ, ψ, ε]
    rw [GlobalTheory.NormRos.prod_square, GlobalTheory.NormRos.prod_square]
    dsimp [rosatiφ, rosatiε, padd]
    simp only [zpow_one, zpow_neg_one, inv_inv]
    change (q ((fst B B ≫ f) * snd B B).left)⁻¹ * q (fst B B ≫ f).left *
      q (snd B B).left * q (fst B B * (snd B B ≫ g)).left *
      (q (fst B B).left)⁻¹ * (q (snd B B ≫ g).left)⁻¹ =
      q (fst B B * (snd B B ≫ g)).left * (q (fst B B).left)⁻¹ *
      (q (snd B B ≫ g).left)⁻¹ * q (1 : (B ⊗ B) ⟶ B).left *
      (q ((fst B B ≫ f) * snd B B).left * (q (fst B B ≫ f).left)⁻¹ *
      (q (snd B B).left)⁻¹ * q (1 : (B ⊗ B) ⟶ B).left)⁻¹
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have chart : ChartPull (LB.div (LB.LinComb M ψ ε) (LB.LinComb M φ ε))
      (LB.LinComb M (Sum.elim ψ φ) (Sum.elim ε fun k => -ε k)) (𝟙 _) := by
    have le : ∀ p : (_ → M.ι) × (_ → M.ι), LB.wchart M ψ p.1 ⊓ LB.wchart M φ p.2 ≤
        LB.wchart M (Sum.elim ψ φ) (Sum.elim p.1 p.2) := fun p y hy => Set.mem_iInter.2 fun k => by
      rcases k with k | k
      exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
    refine { idx := fun p => Sum.elim p.1 p.2, le := le, g := ?_ }
    intro y p q hp hq
    refine (gm_div _ _ (𝟙 _) y p q ⟨hp, hq⟩).trans (Eq.trans ?_
      (gm_linComb M _ _ (𝟙 _) y _ _ (le p hp) (le q hq)).symm)
    refine (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb M ψ ε (𝟙 _) y p.1 q.1 hp.1 hq.1)
      (gm_linComb M φ ε (𝟙 _) y p.2 q.2 hp.2 hq.2)).trans ?_
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rfl
  obtain ⟨v, hv⟩ := hh'
  exact gen_chartPull chart v hv

theorem rosatiAdj_of_lbIso : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (f g : B ⟶ B), M.IsLB → LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) → RosatiAdj B M f g := by
  intro S B _ _ M f g hM h
  have H := GlobalTheory.NormRos.exists_gen_rosati hM f g h
  intro s
  exact ⟨⊤, trivial, MulPull.HasGen.pull H ((B ⊗ B).hom ⁻¹ᵁ ⊤).ι⟩

end GlobalTheory.AdjPolLocal
