module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactIsOpenCosVN
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.AdmCpt
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.DecN

open NumberField IsDedekindDomain GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec
open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport
open scoped Topology

variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem exists_box_combN {n M : ℕ} (g : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (hg : IsSB g) :
    ∃ (s : Finset (Fin n → Fin M → Af F ⊗[F] E))
      (A : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
      (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ a v, IsCompact (A a v) ∧ IsOpen (A a v)) ∧ (∀ a ∈ s, ∀ v, v ∉ S → A a v = latV b v) ∧
        ∀ Y, g Y = ∑ a ∈ s, g a * (boxF (A a)).indicator (fun _ => (1 : ℂ)) Y := by
  apply _root_.GlobalTheory.CompanionTheory.PfSWUS.FockSplit.Box.exists_box_combN <;> assumption

theorem isSchwartzArch_const_mulN {n M : ℕ} {φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ} (h : IsSchwartzArch φ) (c : ℂ) :
    IsSchwartzArch fun X => φ X * c := by
  obtain ⟨N, e, c1, c2, f, hf⟩ := h
  exact ⟨N, e, c1, c2, c • f, fun X => by simp [hf X, mul_comm]⟩

end GlobalTheory.CompanionTheory.WhitFree.DecN

namespace GlobalTheory.CompanionTheory.WhitFree

theorem schwartzBruhat_eq_sum_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → ∃ (k : ℕ) (φ : Fin k → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin k → (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ d b Φ hΦ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨k', Φinf, Φf, hi, hf, hs⟩ := hΦ
  choose s A S hA hS hdec using fun i => DecN.exists_box_combN b (Φf i) (hf i)
  let I := Σ i : Fin k', ↥(s i)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun j X => Φinf (e.symm j).1 X * Φf (e.symm j).1 (e.symm j).2.1,
    fun j => A (e.symm j).1 (e.symm j).2.1, Finset.univ.biUnion S, fun j => ?_, fun j v => hA _ _ v,
    fun j v hv => ?_, fun X => ?_⟩
  · exact DecN.isSchwartzArch_const_mulN (hi _) _
  · refine hS _ _ (e.symm j).2.2 v fun h => hv (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩)
  · rw [hs X, Fintype.sum_equiv e.symm _ (fun p : I => pureN (fun Y => Φinf p.1 Y * Φf p.1 p.2.1) (A p.1 p.2.1) X)
      (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdec i (projFin X), Finset.mul_sum, ← Finset.sum_coe_sort (s i)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [pureN, mul_assoc]
    rfl

end GlobalTheory.CompanionTheory.WhitFree
