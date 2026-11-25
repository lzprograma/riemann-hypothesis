module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaModuleSaturationTheorem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHom

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem sen_push_pre_le : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (B A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (w w' : ZMod n → ℤ) (N : Lats k n B.m), F.Obj B → IsHom A₁ B j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → ABC (F.D B) w w' N → ∀ i x, sen ((F.D A).γ i) (F.push A₁ A p (F.pre A₁ B j N) i) x ≤ sen ((F.D B).γ i) (N i) x := by
  intro k G _ _ l n _ _ _ R F B A₁ A j p w w' N hB hj hji hp hps hN i x
  have hA₁ : F.Obj A₁ := F.obj_sub A₁ B j hj hji hB
  obtain ⟨C, q, hq, hqs, hex⟩ := GlobalTheory.Models.SubModel.exists_coker A₁ B j hj
  obtain ⟨K, s, hs, hsi, hex'⟩ := GlobalTheory.Models.SubModel.exists_ker A₁ A p hp
  have h1 := _root_.GlobalTheory.Models.sen_eq_sen_pre_add_sen_push F A₁ B C j q N hB hj hq hji hqs hex i (hN.1 i) (hN.2.2 i) x
  have hsat := GlobalTheory.PhiGam.Sat.main R (F.D B) (F.D A₁) (F.map A₁ B j) (F.map_inj A₁ B j hA₁ hB hj hji)
    (F.map_φ A₁ B j hA₁ hB hj) (F.map_γ A₁ B j hA₁ hB hj) w w' N hN.1 hN.2.1 hN.2.2
  have h2 := _root_.GlobalTheory.Models.sen_eq_sen_pre_add_sen_push F K A₁ A s p (F.pre A₁ B j N) hA₁ hs hp hsi hps hex' i (hsat.1 i) (hsat.2.2 i) x
  omega

end GlobalTheory.Models
