module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsEps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriLift

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

theorem UpperTheory.V.Loc.crLift :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ r' : GQ l →* GG (m := 3) (R := B'), D.InDcr (π' : B' →+* E) r' → ∃ r : GQ l →* GG (m := 3) (R := B), D.InDcr (π : B →+* E) r ∧ (GG.map (p : B →+* B')).comp r = r' := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hc r' hr'
  obtain ⟨u', n', hu', hn1, hn2, rfl⟩ := (ordEq hP D E B' π' hπ' r').1 hr'
  obtain ⟨u, hu, rfl⟩ := triLift hP D E B π hπ B' π' hπ' p hp hc u' hu'
  obtain ⟨n, hn, rfl⟩ := _root_.UpperTheory.V.Loc.OrdinaryDeformation.lift_lower (p : B →+* B') hp n' hn2
  refine ⟨conjBy n u, (ordEq hP D E B π hπ _).2 ⟨u, n, hu, fun a b => ?_, hn, rfl⟩, UpperTheory.V.Loc.OrdinaryDeformation.map_conjBy _ n u⟩
  have h := hn1 a b
  rw [RingHom.mem_ker] at h ⊢
  rw [← h, ← hc, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
  change π' (p _) = π' (p _ - _)
  congr 1
  split_ifs <;> simp
