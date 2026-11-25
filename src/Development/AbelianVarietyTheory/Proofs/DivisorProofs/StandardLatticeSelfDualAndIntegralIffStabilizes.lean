module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTransferPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

open GlobalTheory.NormRatio

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.NormRatio.StdLevel

variable {D : D7}

def intSub (D : D7) : Subring (Af D.host.F ⊗[D.host.F] D.host.E) where
  carrier := intAE D
  mul_mem' := GlobalTheory.HostAdeleIso.intAE_mul_mem D
  one_mem' := AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩
  add_mem' := (intAE D).add_mem
  zero_mem' := (intAE D).zero_mem
  neg_mem' := (intAE D).neg_mem

theorem mem_intAE_iff_swap (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ intAE D ↔ Lev.swapAE D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      have e : Lev.swapAE D (a ⊗ₜ[D.host.F] (x : D.host.E)) =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
      rw [e]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
    | zero => rw [RingHom.map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [RingHom.map_add (f := _)]; exact add_mem hy hz
    | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy
  · intro hz
    let c := (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toRingEquiv.toRingHom
    have key : Formalism.L2.Herm.intAf D.host.F D.host.E ≤ (intSub D).comap c := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · exact AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, rfl⟩
      · exact AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, rfl⟩
    have e : ∀ w, c (Lev.swapAE D w) = w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [RingHom.map_zero, RingHom.map_zero]
      | tmul a b => rfl
      | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
    have h : c (Lev.swapAE D z) ∈ intSub D := key hz
    rw [e] at h
    exact h

theorem preserves_iff {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (M M' : Matrix (Fin n) (Fin n) R)
    (h1 : M * M' = 1) (h2 : M' * M = 1) :
    (∀ y : Fin n → R, (∀ i, y i ∈ S) ↔ ∀ i, (M *ᵥ y) i ∈ S) ↔ (∀ i j, M i j ∈ S) ∧ ∀ i j, M' i j ∈ S := by
  intros
  apply _root_.GlobalTheory.TransferHyp.stab_iff_entries <;> assumption

theorem mem_latHat_stdLat (V : HSp D) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((stdLat V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
      Set (Fin V.rank → D.host.E)) ↔ ∀ i, z i ∈ intAE D := by
  apply _root_.GlobalTheory.ClassScalarValue.mem_latHat_std <;> assumption

theorem stdLat_eq (V : HSp D) : stdLat V = GlobalTheory.SW.stdL D.host.E V.rank := by
  ext x
  rw [GlobalTheory.SW.Base.mem_stdL]
  simp only [stdLat, Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun i => ?_
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x i, h⟩, rfl⟩⟩

end GlobalTheory.NormRatio.StdLevel


open GlobalTheory.NormRatio.StdLevel in
theorem GlobalTheory.NormRatio.selfDual_and_mem_intG_iff : ∀ {D : D7} (V : HSp D) (n : ℕ) (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n),
    V.gram = 1 → V.rank = n → GlobalTheory.BotFormula.IsFinPt V g x →
    IsSelfDualC V (stdLat V) ∧ (x ∈ intG D n ↔ g ∈ openOff V (stdLat V) ∅) := by
  intro D V n g x hG hn hx
  subst hn
  have hSD : IsSelfDualC V (stdLat V) := by rw [stdLat_eq]; exact GlobalTheory.Ker.Base.selfDualC_stdL hG
  refine ⟨hSD, ?_⟩
  have hfx := GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hx
  subst hfx
  have e1 : ∀ (k : GA D V) (i j : Fin V.rank),
      (((GlobalTheory.BotClassDict.finStd V hG k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔
        (finHom V k).1 i j ∈ intAE D := fun k i j => by
    rw [← GlobalTheory.BotClassDict.toAfE_int_iff, GlobalTheory.BotClassDict.toAfE_finStd, mem_intAE_iff_swap]
  have hL : GlobalTheory.BotClassDict.finStd V hG g ∈ intG D V.rank ↔
      (∀ i j, (finHom V g).1 i j ∈ intAE D) ∧ ∀ i j, (finHom V g⁻¹).1 i j ∈ intAE D := by
    rw [GlobalTheory.NormSum.mem_intG]
    unfold Formalism.MainNotions.StandardLatticesGL3.IntG
    have e2 : ((↑(GlobalTheory.BotClassDict.finStd V hG g) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) =
        ↑(GlobalTheory.BotClassDict.finStd V hG g⁻¹) := by rw [map_inv, Subgroup.coe_inv]
    rw [e2]
    simp only [e1]
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  have hR : g ∈ openOff V (stdLat V) ∅ ↔
      ∀ y, (∀ i, y i ∈ intAE D) ↔ ∀ i, ((finHom V g).1 *ᵥ y) i ∈ intAE D := by
    have e : g ∈ openOff V (stdLat V) ∅ ↔ g ∈ GlobalTheory.AdelicU.levelOpen _ (HSpace.gram V) (stdLat V) := by
      rw [GlobalTheory.AdelicU.mem_levelOpen]; simp [openOff]
    haveI := hSD.1
    rw [e, GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ (Submodule.IsLattice.fg D.host.E (stdLat V))]
    refine forall_congr' fun y => ?_
    rw [mem_latHat_stdLat, mem_latHat_stdLat]
    rfl
  have h1 : (finHom V g).1 * (finHom V g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h2 : (finHom V g⁻¹).1 * (finHom V g).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  rw [hL, hR]
  exact (preserves_iff (intSub D) _ _ h1 h2).symm
