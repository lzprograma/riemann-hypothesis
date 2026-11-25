module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

noncomputable section

namespace GlobalTheory.StdUnn.HeightExists

variable {D : D7} {n : ℕ}

theorem lower_eq_zero {p : G D n} (hp : p ∈ P D n) (i j : Fin n) :
    mat p (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := by
  apply _root_.GlobalTheory.StdUnn.Model.lower_eq_zero <;> assumption

theorem blkA_mul {p q : G D n} (hq : q ∈ P D n) : blkA (mat (p * q)) = blkA (mat p) * blkA (mat q) := by
  exact GlobalTheory.StdUnn.Model.blkA_mul hq

theorem blkA_one : blkA (mat (1 : G D n)) = 1 := GlobalTheory.StdUnn.Model.blkA_one

def leviBlock : P D n →* GL (Fin n) (AE D) :=
  MonoidHom.toHomUnits ⟨⟨fun p => blkA (mat p.1), blkA_one⟩, fun p q => blkA_mul q.2⟩

theorem continuous_mat : Continuous (mat : G D n → Mx D (n + n) (n + n)) :=
  Units.continuous_val.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous

theorem continuous_leviBlock : Continuous (leviBlock (D := D) (n := n)) := by
  have hA : Continuous fun g : G D n => blkA (mat g) :=
    continuous_matrix fun i j => continuous_mat.matrix_elem _ _
  rw [Units.continuous_iff]
  refine ⟨hA.comp continuous_subtype_val, ?_⟩
  refine (hA.comp (continuous_subtype_val.comp continuous_inv)).congr fun p => ?_
  rw [← map_inv]; rfl

theorem continuous_detGL : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE D) → (AE D)ˣ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  rw [Units.continuous_iff]
  refine ⟨Units.continuous_val.matrix_det, (Units.continuous_coe_inv.matrix_det).congr fun g => ?_⟩
  rw [← map_inv]; rfl

theorem isCompact_K : IsCompact (K D n : Set (G D n)) := GlobalTheory.StdUnn.Model.isCompact_K

theorem isClosed_P : IsClosed (P D n : Set (G D n)) := by
  apply _root_.GlobalTheory.StdUnn.Model.isClosed_P <;> assumption

end GlobalTheory.StdUnn.HeightExists

namespace GlobalTheory.StdUnn


open HeightExists in
theorem exists_height : ∀ (D : D7) (n : ℕ), ∃ H : G D n → ℝ≥0, IsHeight H := by
  intro D n
  let δ : P D n →* ℝ≥0 := (absA D).comp (Matrix.GeneralLinearGroup.det.comp leviBlock)
  have hc : Continuous δ := continuous_absE.comp (continuous_detGL.comp continuous_leviBlock)
  haveI := t2Space_adeleRing' (F := D.host.F)
  have ht := triv_of_isCompact (δ := δ) isClosed_P hc isCompact_K
  refine ⟨iwAbs δ (K D n), fun p hp a ha k hk => ?_⟩
  rw [show a = leviBlock (D := D) (n := n) ⟨p, hp⟩ from Units.ext ha.symm]
  exact iwAbs_mul_of_triv ht ⟨p, hp⟩ hk

end GlobalTheory.StdUnn

end
