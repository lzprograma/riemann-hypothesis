module

import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdTr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight

@[expose] public section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_eq_add (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + σ x := by
  apply Formalism.L2.SG.Pf.NcVal.TrW.trace_eq_add <;> assumption

variable (v : HeightOneSpectrum (𝓞 F))

theorem trace_v (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (w : Fv F v ⊗[F] E) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + sigR (Fv F v) σ w := by
  apply _root_.Formalism.L2.SG.Pf.NcVal.TrW.trace_v <;> assumption

theorem sigR_sigR (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (w : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (sigR (Fv F v) σ w) = w := by
  induction w using TensorProduct.inductionOn with
  | tmul c e => simp [sigR, hinv]
  | add w1 w2 h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2]

theorem b_inclR_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

theorem b_smul_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : c • x ∈ OEv (E := E) v :=
  Submodule.smul_mem (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (⟨c, hc⟩ : v.adicCompletionIntegers F) hx

theorem b_one_mem : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  simpa using b_inclR_mem (E := E) v 1

theorem b_sc_eq (c : Fv F v) : sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := rfl

theorem b_sc_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) : sc (E := E) v c ∈ OEv (E := E) v := by
  rw [b_sc_eq, Algebra.algebraMap_eq_smul_one]
  exact b_smul_mem v hc (b_one_mem v)

theorem b_mul_mem {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  first | exact _root_.PI.OmLocU.oEv_mul | (apply _root_.PI.OmLocU.oEv_mul <;> assumption)

theorem b_trace_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x ∈ v.adicCompletionIntegers F := by
  apply _root_.Formalism.L2.SG.Pf.NcVal.TrW.trace_mem <;> assumption

theorem b_lat_smul {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {o : Fv F v ⊗[F] E} (ho : o ∈ OEv (E := E) v)
    {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v (L : Set (Fin n → E))) :
    o • x ∈ latLoc (E := E) v (L : Set (Fin n → E)) := by
  unfold OEv at ho
  rw [SetLike.mem_coe] at ho
  induction ho using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, -, rfl⟩ := hy
    unfold latLoc at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      have hel : e • l ∈ L := L.smul_mem e hl
      have eq : inclR (F := F) (Fv F v) (e : E) • ratV (F := F) (Fv F v) l =
          ratV (F := F) (Fv F v) (e • l) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, ratV]
        rw [← map_mul]
        rfl
      rw [eq]
      exact Submodule.subset_span ⟨_, hel, rfl⟩
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add z w _ _ hz hw =>
      rw [smul_add]
      exact Submodule.add_mem _ hz hw
    | smul r z _ hz =>
      rw [smul_comm]
      exact Submodule.smul_mem _ r hz
  | zero =>
    rw [zero_smul]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [add_smul]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ r hy

theorem b_sig_sig (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h4, h4, star_star]

theorem b_sig_nt (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hn
  push Not at hn
  have hs : σ = AlgHom.id F E := AlgHom.ext hn
  obtain ⟨-, htc, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h4 τ x
    rw [hs, AlgHom.id_apply] at this
    rw [starRingEnd_apply]; exact this.symm
  exact InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 hr)

end Gen

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def TrPerf : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ z : Fv F v ⊗[F] E,
    (∀ x ∈ OEv (E := E) v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * z) ∈ v.adicCompletionIntegers F) →
    z ∈ OEv (E := E) v

end Steps

end PI.OmLocU.SdB
