module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (E) in
def OE (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (v.adicCompletion F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a ∈ v.adicCompletionIntegers F, ∃ o : 𝓞 E, z = a ⊗ₜ[F] (o : E)}


variable (E) in
def lat (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : AddSubgroup (Fin n → v.adicCompletion F ⊗[F] E) :=
  AddSubgroup.pi Set.univ fun _ => OE E v

def latM (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) :
    AddSubgroup (Fin n → v.adicCompletion F ⊗[F] E) :=
  (lat E v n).map M.mulVecLin.toAddMonoidHom

theorem sigR_eq_cA (z : AE F E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ z = cA σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, cA, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem bottom_onto {S : Type} [CommRing S] (O : Subring S) {n : Type} [Fintype n] [DecidableEq n]
    (k k' : Matrix (n ⊕ n) (n ⊕ n) S) (hkk : k * k' = 1) (hk : ∀ i j, k i j ∈ O) (hk' : ∀ i j, k' i j ∈ O) (y : n → S)
    (hy : ∀ i, y i ∈ O) : ∃ y₁ y₂ : n → S, (∀ i, y₁ i ∈ O) ∧ (∀ i, y₂ i ∈ O) ∧
      k.toBlocks₂₁.mulVec y₁ + k.toBlocks₂₂.mulVec y₂ = y := by
  classical
  set z := k'.mulVec (Sum.elim (0 : n → S) y) with hz
  have hzO : ∀ j, z j ∈ O := fun j => by
    simp only [hz, Matrix.mulVec, dotProduct]
    exact O.sum_mem fun c _ => O.mul_mem (hk' j c) (by cases c <;> simp [hy, O.zero_mem])
  refine ⟨fun i => z (Sum.inl i), fun i => z (Sum.inr i), fun i => hzO _, fun i => hzO _, ?_⟩
  have hkz : k.mulVec z = Sum.elim (0 : n → S) y := by rw [hz, Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]
  funext i
  have := congrFun hkz (Sum.inr i)
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inr] at this
  simpa [Matrix.mulVec, dotProduct, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂] using this

end PositivityTheory.SiegelWeilFormula.KWhit.Ht

end
