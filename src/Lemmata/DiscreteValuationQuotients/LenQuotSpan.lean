module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

universe u_1 u_2

namespace Bl.DiscreteValuationQuotients

private lemma lenQuotSpan {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (x : O) :
    Module.length O (O ⧸ Ideal.span ({x} : Set O)) = IsDiscreteValuationRing.addVal O x := by
  rw [Module.length_quotient, ← Order.coheight_orderIso (IsDiscreteValuationRing.idealOrderIsoENat O)]
  exact (Order.height_enat _).trans <| (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2
    (Submodule.IsPrincipal.associated_generator_span_self x)

theorem goal1 :
  ∀ {O : Type u_1} {M : Type u_2} [CommRing.{u_1} O] [IsDomain.{u_1} O]
  [IsDiscreteValuationRing.{u_1} O] [AddCommGroup.{u_2} M] [Module.{u_1, u_2} O M]
  [Module.Free.{u_1, u_2} O M] [Module.Finite.{u_1, u_2} O M]
  (φ : LinearMap.{u_1, u_1, u_2, u_2} (RingHom.id.{u_1} O) M M),
  Function.Injective.{u_2 + 1, u_2 + 1} (DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1} φ) →
    Eq.{1} (Module.length.{u_1, u_2} O (HasQuotient.Quotient.{u_2, u_2} M (LinearMap.range.{u_1, u_1, u_2, u_2} φ)))
      (DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O)
        (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_2 + 1, u_1 + 1} LinearMap.det.{u_2, u_1} φ)) := by
  intro O M _ _ _ _ _ _ _ φ hφ
  classical
  let e0 : M ≃ₗ[O] LinearMap.range φ := LinearEquiv.ofInjective φ hφ
  have h : Module.finrank O (LinearMap.range φ) = Module.finrank O M := e0.finrank_eq.symm
  let b := Module.Free.chooseBasis O M
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[O] LinearMap.range φ := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[O] M := (LinearMap.range φ).subtype ∘ₗ (e' : M →ₗ[O] LinearMap.range φ)
  have hφf : φ = (LinearMap.range φ).subtype ∘ₗ (e0 : M →ₗ[O] LinearMap.range φ) :=
    LinearMap.ext fun x => rfl
  have hassoc : Associated (LinearMap.det φ) (LinearMap.det f) := by
    rw [hφf]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _) (b' i) : LinearMap.range φ) : M) = _
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    have hf : f ∘ b' = fun i => a i • b' i := funext ha
    simpa only [← hf, Module.Basis.det_comp, Module.Basis.det_self, smul_eq_mul, mul_one] using
      b'.det.map_smul_univ a b'
  have hval : IsDiscreteValuationRing.addVal O (LinearMap.det φ) =
      IsDiscreteValuationRing.addVal O (∏ i, a i) := by
    rw [← hdet]
    exact (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 hassoc
  rw [(Submodule.quotientEquivPiSpan (LinearMap.range φ) b h).length_eq,
    Module.length_pi_of_fintype, hval]
  exact (Finset.sum_congr rfl fun i _ => lenQuotSpan (a i)).trans
    (map_prod (AddValuation.toValuation (IsDiscreteValuationRing.addVal O)) a Finset.univ).symm

end Bl.DiscreteValuationQuotients
