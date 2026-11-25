module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SingleMemSubmodule
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyClauseStatement

@[expose] public section

section SlopeTestRemainingChoices

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia

private theorem roots {k : Type} [Field k] (a b : kˣ) (h : ∀ n : ℕ, ((a * b ^ n : kˣ) : k) + 1 + (((a * b ^ n)⁻¹ : kˣ) : k) = 0) :
    (b : k) ^ 2 - 1 = 0 := by
  have h' : ∀ n : ℕ, ((a : k) * b ^ n) ^ 2 + a * b ^ n + 1 = 0 := fun n => by
    have e := (a * b ^ n).mul_inv
    have e' := h n
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at e e'
    linear_combination ((a : k) * b ^ n) * e' - e
  by_contra hb
  have hb1 : (b : k) - 1 ≠ 0 := fun e => hb (by linear_combination ((b : k) + 1) * e)
  have e1 : (a : k) * b + a + 1 = 0 := mul_left_cancel₀ (mul_ne_zero a.ne_zero hb1) (by linear_combination h' 1 - h' 0)
  have e2 : (a : k) * b ^ 2 + a + 1 = 0 := mul_left_cancel₀ (mul_ne_zero a.ne_zero hb) (by linear_combination h' 2 - h' 0)
  exact mul_ne_zero (mul_ne_zero a.ne_zero b.ne_zero) hb1 (by linear_combination e2 - e1)

private theorem conj_mat {G R : Type} [Group G] [CommRing R] (h : GL (Fin 3) R) (r : G →* GG (m := 3) (R := R)) {g : G}
    (hg : (r g).right = 1) : (conjBy h r g).mat = (h : Matrix _ _ R) * (r g).mat * ((h⁻¹ : GL (Fin 3) R) : Matrix _ _ R) := by
  simp [conjBy, GG.mat, hg]

private theorem frame {O A K G : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [Field K]
    [Algebra O K] [FaithfulSMul O K] [Group G] (j : A →ₐ[O] K) (hj : Function.Injective j) (η : G →* ℤˣ) (Ψ : G →* Oˣ)
    (D : Subgroup G) (I : Subgroup D) (r' : G →* GG (m := 3) (R := A)) (hpt : Red η Ψ r')
    (ht : CondT (η.comp D.subtype) (Ψ.comp D.subtype) I (r'.comp D.subtype))
    (hI : TypeI η (UpperTheory.V.UnitaryThreeInertia.push j r')) (U : Subgroup G) [U.Normal]
    (hU : U ≤ η.ker) (x : D) (hx : η x = 1) (hx' : IsUnit ((Ψ x : O) ^ 2 - 1))
    (u : D) (hu : u ∈ I) (huU : u.1 ∈ U) (hu' : Ψ u ^ 2 ≠ 1) : MatIrr U (mats (UpperTheory.V.UnitaryThreeInertia.push j r')) := by
  by_contra hc
  obtain ⟨h, -, htri⟩ := ht
  set P : GL (Fin 3) K := GeneralLinearGroup.map (j : A →+* K) h⁻¹ with hP
  have em : ∀ s, mats (UpperTheory.V.UnitaryThreeInertia.push j r') s = (r' s).mat.map j := fun _ => rfl
  have key : ∀ s : D, η s = 1 → (P : Matrix _ _ K) * mats (UpperTheory.V.UnitaryThreeInertia.push j r') s * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K) =
      (conjBy h⁻¹ (r'.comp D.subtype) s).mat.map j := fun s hs => by
    rw [conj_mat h⁻¹ (r'.comp D.subtype) (g := s) ((hpt.mult _).trans hs), hP, ← map_inv, em]
    symm
    refine (Matrix.map_mul (f := (j : A →+* K))).trans ?_
    rw [Matrix.map_mul]
    rfl
  have tri : ∀ s : D, η s = 1 →
      ((P : Matrix _ _ K) * mats (UpperTheory.V.UnitaryThreeInertia.push j r') s * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K)).BlockTriangular id :=
    fun s hs i j hij => by
    rw [key s hs, map_apply, htri.tri s hs i j (by
      have : (j : ℕ) < i := hij
      simp only [wt, wt1]
      omega), map_zero]
  have hu1 : η u = 1 := hU huU
  have hinj : Function.Injective
      ((P : Matrix _ _ K) * mats (UpperTheory.V.UnitaryThreeInertia.push j r') u * ((P⁻¹ : GL (Fin 3) K) : Matrix _ _ K)).diag := by
    intro i j hij
    rw [diag_apply, diag_apply, key u hu1, map_apply, map_apply, htri.ine u hu hu1, htri.ine u hu hu1,
      AlgHom.commutes, AlgHom.commutes] at hij
    have e : Ψ u ^ wt1 i = Ψ u ^ wt1 j := Units.ext (FaithfulSMul.algebraMap_injective O K hij)
    generalize Ψ u = y at e hu'
    have h1 : y ≠ 1 := fun h => hu' (by rw [h, one_pow])
    have h2 : y ≠ y⁻¹ := fun h => hu' (by rw [sq, ← eq_inv_iff_mul_eq_one]; exact h)
    fin_cases i <;> fin_cases j <;> simp [wt1, h1, h2, h1.symm, h2.symm] at e ⊢
  obtain ⟨g, hg, hz⟩ := exists_trace_mul_pow_eq_zero_of_reducible_restriction
    η.ker U hU (mats (UpperTheory.V.UnitaryThreeInertia.push j r')) (fun a ha b _ => by
      have : (UpperTheory.V.UnitaryThreeInertia.push j r' a).right = 1 := (hpt.mult a).trans ha
      simp only [mats, GG.mat, map_mul, SemidirectProduct.mul_left, this, sgnAct_one, Units.val_mul])
    (by simp only [mats, GG.mat, map_one, SemidirectProduct.one_left, Units.val_one]) P.inv_mul P.mul_inv huU (tri u hu1) hinj
    hI hc (x := x.1) hx (tri x hx)
  let φ : O →+* ResidueField A := (residue A).comp (algebraMap O A)
  refine (hx'.map φ).ne_zero ?_
  rw [map_sub, map_pow, map_one]
  refine roots (Units.map φ.toMonoidHom (Ψ g)) (Units.map φ.toMonoidHom (Ψ x)) fun n => ?_
  have e := hz n
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_inv]
  generalize g * x.1 ^ n = y at e
  have e1 : (r' y).mat.trace = 0 := by
    refine hj ?_

    rw [map_zero, ← e, trace, trace, map_sum]
    rfl
  have e2 : ∀ i, residue A ((r' y).mat i i) = φ ((r0 η Ψ y).mat i i) := fun i =>
    Ideal.Quotient.eq.2 (hpt.red y i i)
  have e3 := congrArg (residue A) e1
  rw [trace_fin_three, map_add (f := _), map_add (f := _), e2, e2, e2, map_zero] at e3
  simpa [GG.mat, tor_val, wt1] using e3

end SlopeTestRemainingChoices

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.V.Pr.matIrr_open_gd :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (g₁ : G ℚ Ω), D.Marked g₁ →
    ∀ (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 → ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG (m := 3) (R := A)), OrdPt l D.η D.Ψ D.cc g₁ B r → TypeI D.η (UnitaryThreeInertia.push A.val r) →
      ∀ V : Subgroup (G ℚ Ω), IsOpen (V : Set (G ℚ Ω)) → V ≤ D.η.ker → MatIrr V (mats (UnitaryThreeInertia.push A.val r)) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ D g₁ _ B hv A _ _ r hr hI U hU hUη
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  have : Finite (G ℚ Ω ⧸ U) := U.quotient_finite_of_isOpen hU
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨hη, x, hx, hx'⟩ := (dat_facts D).2.2.2.2.2.2.2.2.2.2 B hv
  have hu : IsUnit (1 + (l : ℤ_[l])) := by
    simpa using isUnit_one_sub_self_of_mem_nonunits (-(l : ℤ_[l])) (by simpa using PadicInt.prime_p.not_unit)
  obtain ⟨σ, hσ, hσ'⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l B hv hu.unit
  set m := U.normalCore.index * Nat.card (ZMod N)ˣ with hm
  have hm0 : m ≠ 0 := mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Nat.card_pos.ne'
  have hσm : σ ^ m ∈ Ine (F := ℚ) B := pow_mem hσ m
  have key := frame A.val Subtype.val_injective D.η D.Ψ _ _ r hr.red hr.ord hI U.normalCore
    (U.normalCore_le.trans hUη) ⟨x, Ine_le_Dec B hx⟩ (hη hx) hx' ⟨σ ^ m, Ine_le_Dec B hσm⟩
    (by rw [Subgroup.mem_subgroupOf]; exact hσm)
    (by
      show σ ^ m ∈ _
      rw [hm, pow_mul]
      exact pow_mem (Subgroup.pow_index_mem _ σ) _)
    (by
      show Chr.Psi l e (Chr.dirG ℚ Ω ψ) (σ ^ m) ^ 2 ≠ 1
      have h1 : Chr.dirG ℚ Ω ψ (σ ^ m) = 1 := by
        rw [Chr.dirG, MonoidHom.comp_apply, map_pow, hm, pow_mul', pow_card_eq_one', one_pow, map_one]
      rw [Chr.Psi, MonoidHom.mul_apply, h1, mul_one, MonoidHom.zpow_apply, zpow_natCast, map_pow, ← pow_mul,
        ← pow_mul]
      intro h
      have h2 := congrArg (fun y : (c.O)ˣ => ((y : c.O) : PadicAlgCl l)) h
      simp only [Base.chiO, MonoidHom.comp_apply, hσ', Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec] at h2
      have h3 : (((1 + l) ^ (m * (e * 2)) : ℕ) : PadicAlgCl l) = (1 : ℕ) := by simpa using h2
      have h4 := Nat.cast_injective h3
      have := D.gd.e_pos
      have := hl.out.pos
      rw [Nat.pow_eq_one] at h4
      rcases h4 with h4 | h4
      · omega
      · exact mul_ne_zero hm0 (by omega) h4)
  exact fun W hW => key W fun g hg => hW g (U.normalCore_le hg)
