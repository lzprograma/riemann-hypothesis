module

public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Lemma
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
import Lemmata.GeneralBFactFurther.Imports
import Mathlib.RingTheory.MvPolynomial.Localization
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylRowStable
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

@[expose] public section

namespace Bl.DualWeylPullback

private lemma colAddGen_map {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {k n : ℕ}
    (l j : Fin n) (f : MvPolynomial (Fin k × Fin n) O) :
    MvPolynomial.map φ (Formalism.GradedWeylDivisibility.colAddGen O l j f) = Formalism.GradedWeylDivisibility.colAddGen K l j (MvPolynomial.map φ f) := by
  unfold Formalism.GradedWeylDivisibility.colAddGen
  rw [MvPolynomial.map_aeval_eq_aeval_map φ (MvPolynomial.map φ) (by ext; simp)]
  congr 1
  congr 1
  funext v
  split_ifs <;> simp

private lemma dualWeyl_pull {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K)
    (hφ : Function.Injective φ) {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) O)
    (hf : MvPolynomial.map φ f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, MvPolynomial.mem_weightedHomogeneousSubmodule] at hf ⊢
  refine ⟨?_, ?_⟩
  · intro d hd
    exact hf.1 (by
      rw [MvPolynomial.coeff_map]
      intro h0
      exact hd (hφ (by rw [h0, map_zero])))
  · intro l j hlj
    apply MvPolynomial.map_injective φ hφ
    rw [colAddGen_map, MvPolynomial.map_rename]
    exact hf.2 l j hlj

private lemma span_unit {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hφ : Function.Injective (algebraMap O K)) {k : ℕ} (g g' : Matrix (Fin k) (Fin k) K)
    (hg : IsUnit g.det) (h : Formalism.MainNotions.G.colSpan O g = Formalism.MainNotions.G.colSpan O g') :
    ∃ A : Matrix (Fin k) (Fin k) O, IsUnit A.det ∧ g' = g * A.map (algebraMap O K) := by
  obtain ⟨A, hA⟩ := Formalism.MainNotions.G.LatticeSystems.la_factor g g' h.ge
  obtain ⟨B, hB⟩ := Formalism.MainNotions.G.LatticeSystems.la_factor g' g h.le
  refine ⟨A, ?_, hA⟩
  have h1 : g * (A * B).map (algebraMap O K) = g * 1 := by
    rw [Matrix.map_mul, ← Matrix.mul_assoc, ← hA, ← hB, Matrix.mul_one]
  have h2 : (A * B).map (algebraMap O K) = 1 := by
    have h3 := congrArg (fun M => g⁻¹ * M) h1
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg] using h3
  have h3 : A * B = 1 := Matrix.map_injective hφ (by simpa using h2)
  have h4 : A.det * B.det = 1 := by rw [← Matrix.det_mul, h3, Matrix.det_one]
  exact ⟨⟨A.det, B.det, h4, by rw [mul_comm]; exact h4⟩, rfl⟩

private lemma clear_den {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (w : O) (hw : Irreducible w) {σ : Type} (G : MvPolynomial σ K) :
    ∃ n : ℕ, ∃ G0 : MvPolynomial σ O,
      MvPolynomial.map (algebraMap O K) G0 = algebraMap O K (w ^ n) • G := by
  let : IsLocalization.Away w (FractionRing O) := Bl.general_b_fact_further.goal1 hw
  let : IsLocalization.Away w K :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers w)
      (IsLocalization.algEquiv (nonZeroDivisors O) (FractionRing O) K)
  let := MvPolynomial.algebraMvPolynomial (R := O) (S := K) (σ := σ)
  obtain ⟨⟨G0, b, hb⟩, h⟩ := IsLocalization.surj
    ((Submonoid.powers w).map (MvPolynomial.C : O →+* MvPolynomial σ O)) G
  obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := hb
  refine ⟨n, G0, ?_⟩
  simpa only [MvPolynomial.algebraMap_def, MvPolynomial.map_C,
    MvPolynomial.smul_eq_C_mul, mul_comm] using h.symm

theorem goal1 :
  ∀ {O K : Type} [inst : CommRing.{0} O] [inst_1 : IsDomain.{0} O] [IsDiscreteValuationRing.{0} O] [inst_3 : Field.{0} K]
  [inst_4 : Algebra.{0, 0} O K] [IsFractionRing.{0, 0} O K] (w : O),
  Irreducible.{0} w →
    ∀ (m : Nat) (mu : Fin (HAdd.hAdd.{0, 0, 0} m 1) → Int),
      Antitone.{0, 0} mu →
        ∀ (g : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) K),
          IsUnit.{0} (Matrix.det.{0, 0} g) →
            ∀ (F : MvPolynomial.{0, 0} (Prod.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1))) K),
              Membership.mem.{0, 0}
                  (Formalism.GradedWeylDivisibility.dualWeyl.{0} K (HAdd.hAdd.{0, 0, 0} m 1) (HAdd.hAdd.{0, 0, 0} m 1) (Formalism.MainNotions.G.nuOf mu)) F →
                Exists.{1} fun (n : Nat) ↦
                  Membership.mem.{0, 0} (Formalism.MainNotions.G.H0.{0, 0} O m mu (Formalism.MainNotions.G.colSpan.{0, 0} O g))
                    (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} w n) F) := by
  intro O K _ _ _ _ _ _ w hw m mu hmu g hg F hF
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hG : g.det ^ mu (Fin.last m) • Formalism.GradedWeylDivisibility.rowAct K g F ∈
      Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (Formalism.MainNotions.G.nuOf mu) :=
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylModuleRowActionStable K _ _ _ g F hF)
  obtain ⟨n, G0, hG0⟩ := clear_den w hw (g.det ^ mu (Fin.last m) • Formalism.GradedWeylDivisibility.rowAct K g F)
  have hG0m : G0 ∈ Formalism.GradedWeylDivisibility.dualWeyl O (m + 1) (m + 1) (Formalism.MainNotions.G.nuOf mu) :=
    dualWeyl_pull _ hinj _ G0 (by rw [hG0]; exact Submodule.smul_mem _ _ hG)
  refine ⟨n, ?_⟩
  unfold Formalism.MainNotions.G.H0
  rw [ite_eq_left hmu]
  simp only [Submodule.mem_iInf]
  rintro g' ⟨hg', hspan⟩
  obtain ⟨A, hA, rfl⟩ := span_unit hinj g g' hg hspan
  rw [Formalism.GradedWeylDivisibility.nabla_twist_mem O K m mu _ hg']
  obtain ⟨U, hU⟩ := hA
  refine ⟨(↑(U ^ mu (Fin.last m)) : O) • Formalism.GradedWeylDivisibility.rowAct O A G0,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylModuleRowActionStable O _ _ _ A G0 hG0m), ?_⟩
  change MvPolynomial.map (algebraMap O K) ((↑(U ^ mu (Fin.last m)) : O) • Formalism.GradedWeylDivisibility.rowAct O A G0) = _
  have hz : algebraMap O K ↑(U ^ mu (Fin.last m)) = (algebraMap O K ↑U) ^ mu (Fin.last m) := by
    have h5 : ((Units.map (algebraMap O K).toMonoidHom (U ^ mu (Fin.last m)) : Kˣ) : K) =
        algebraMap O K ↑(U ^ mu (Fin.last m)) := rfl
    rw [← h5, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hdet : (A.map (algebraMap O K)).det = algebraMap O K A.det := by
    rw [RingHom.map_det]
    rfl
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
    _root_.Formalism.UG.P.wlocal_map_rowAct, hG0, Matrix.det_mul, hdet, ← hU, hz,
    ← Formalism.GradedWeylDivisibility.row_action_mul K (m + 1) (m + 1) (A.map (algebraMap O K)) g, AlgHom.comp_apply,
    ← algebraMap_smul K (w ^ n) F]
  simp only [map_smul, smul_smul]
  congr 1
  rw [mul_zpow]
  ring

end Bl.DualWeylPullback
