module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaRatPair

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  first
  | exact _root_.PositivityTheory.ThKG.Tow.Pln.det_ne_zero_of_hasSig
  | (apply _root_.PositivityTheory.ThKG.Tow.Pln.det_ne_zero_of_hasSig <;> assumption)

theorem det_ne_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r s : ℕ}
    (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ w, HasSig (J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, h0, map_zero]

theorem det_ne_of_sig' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r s : ℕ}
    (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ w, HasSig (Complex.I • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

end GlobalTheory.ThetaRatPair
