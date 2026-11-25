module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Bl.EqIdOfFixed

private lemma ne_id_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) : ∃ y : E, σ y ≠ y := by
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h
  obtain ⟨-, hc, -, hs⟩ := h
  by_contra hne0
  have hne : ∀ z : E, σ z = z := fun z => by_contra fun hz => hne0 ⟨z, hz⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := hc
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext z
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have := hs τ z
  rw [hne z] at this
  exact this.symm

private lemma eq_id_of_fix {F E : Type} [Field F] [Field E] [Algebra F E]
    (hd : Module.finrank F E = 2) (σ : E →ₐ[F] E) {x : E} (hx : σ x = x)
    (hno : ∀ t : F, algebraMap F E t ≠ x) (y : E) : σ y = y := by
  have hli : LinearIndependent F ![(1 : E), x] :=
    (LinearIndependent.pair_iff' one_ne_zero).2 fun t ht =>
      hno t ((Algebra.algebraMap_eq_smul_one t).trans ht)
  have hc : Fintype.card (Fin 2) = Module.finrank F E := by simp [hd]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have heq : σ.toLinearMap = (LinearMap.id : E →ₗ[F] E) := by
    apply b.ext
    intro i
    fin_cases i
    · simp [b]
    · simp [b, hx]
  exact LinearMap.congr_fun heq y

theorem goal1 :
  ∀ {F E : Type} [Field.{0} F] [NumberField.{0} F] [Field.{0} E] [NumberField.{0} E]
  [Algebra.{0, 0} F E] {σ : AlgHom.{0, 0, 0} F E E},
  HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
    ∀ {x : E},
      Eq.{1} (DFunLike.coe.{1, 1, 1} σ x) x →
        Exists.{1} fun (t : F) ↦ Eq.{1} (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} F E) t) x := by
  intro F E _ _ _ _ _ σ h x hx
  by_contra hno0
  have hno : ∀ t : F, algebraMap F E t ≠ x := fun t ht => hno0 ⟨t, ht⟩
  obtain ⟨y, hy⟩ := ne_id_of_cm σ h
  have h' := h
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h'
  exact hy (eq_id_of_fix h'.2.2.1 σ hx hno y)

end Bl.EqIdOfFixed
