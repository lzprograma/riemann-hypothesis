module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem cont_resLe {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {F L : IntermediateField ℚ Ω} (h : F ≤ L) :
    Continuous (resLe h) := by
  letI : Algebra F L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Af.continuous_restrictScalarsHom F L Ω

theorem UpperTheory.V.Ws.Lk.kapCont :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), Continuous P.κ ∧ Continuous P.βL ∧ Continuous P.tL := by
  intro Ω _ _ _ l _ c D T P
  have hβ : Continuous P.βL := P.β_cont.comp (cont_resLe _)
  have ht : Continuous P.tL := P.t_cont.comp (cont_resLe _)
  refine ⟨?_, hβ, ht⟩
  have h0 : Continuous (P.κ₀.comp (resLe (K_le T))) :=
    (_root_.GlobalTheory.HeckeGal.continuous_of_isOpen_ker' P.κ₀ P.κ₀_open).comp (cont_resLe _)
  have h1 : Continuous (P.γ.comp (resQ T.L)) :=
    P.γ_cont.comp (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.L Ω)
  show Continuous fun g => P.κ₀.comp (resLe (K_le T)) g * ((P.γ.comp (resQ T.L)) g)⁻¹ ^ (D.e + 4) * P.βL g ^ (D.e % 2)
  exact (h0.mul ((h1.inv).pow _)).mul (hβ.pow _)
