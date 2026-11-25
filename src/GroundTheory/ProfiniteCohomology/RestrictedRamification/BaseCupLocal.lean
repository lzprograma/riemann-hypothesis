module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.Bockstein
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
import GroundTheory.ProfiniteCohomology.CupProducts.ExistsCocycleMapFEqD
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory NumberField IsDedekindDomain GroundTheory.Global

open scoped DirectSum

noncomputable section

section ULiftCompareAlong

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {A : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep A]
  {B : Rep.{0} (ULift.{0} ℤ) H} [IsDiscreteRep B] {C : Rep.{0} ℤ H} [IsDiscreteRep C]

theorem cohomologyMap_uliftInt_cohomologyMapAlong_of (f : Rep.res φ A ⟶ B) (g : uliftIntToIntRep B ⟶ C)
    (f₂ : Rep.res φ (uliftIntToIntRep A) ⟶ C) (hf : ∀ a : A, g.hom (f.hom a) = f₂.hom a) (m : ℕ)
    (x : cohomology A m) :
    (cohomologyMap g m).hom (cohomologyULiftIntAddEquiv B m ((cohomologyMapAlong φ hφ f m).hom x)) =
      (cohomologyMapAlong φ hφ f₂ m).hom (cohomologyULiftIntAddEquiv A m x) := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A m x
  rw [cohomologyMapAlong_cohomologyπ, cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMap_cohomologyπ,
    cohomologyULiftIntAddEquiv_cohomologyπ', cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesULiftInt]
  funext h
  exact hf _

end ULiftCompareAlong

section Bock

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G)

def resIntRepTriv : Rep.res ψ (intRepTriv G) ⟶ intRepTriv H :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def mulIntRight (A : Rep.{0} (ULift.{0} ℤ) H) : A ⊗ Rep.res ψ (intRepTriv G) ⟶ A :=
  (β_ A (Rep.res ψ (intRepTriv G))).hom ≫ (resIntRepTriv ψ ⊗ₘ 𝟙 A) ≫ intMulPairing H A

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H] in
theorem mulIntRight_tmul (A : Rep.{0} (ULift.{0} ℤ) H) (a : A) (m : ℤ) :
    (mulIntRight ψ A).hom (a ⊗ₜ[ULift.{0} ℤ] (ULift.up m : Rep.res ψ (intRepTriv G)) :
      (A ⊗ Rep.res ψ (intRepTriv G) : Rep _ _)) = m • a :=
  intMulPairing_tmul H A m a

end Bock

section Inv

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (F E : Type) [Field F] [Field E] [Algebra F E]

def galUnitsToZ : uliftIntToIntRep (galUnits.{0} F E) ⟶ galUnitsZ F E :=
  Rep.ofHom ⟨(AddMonoidHom.id (Additive Eˣ)).toIntLinearMap, fun _ => rfl⟩

variable {K : FiniteSubfield}

instance isDiscreteRep_uliftIntToIntRep_galUnits_adic (v : HeightOneSpectrum (𝓞 K.1)) :
    IsDiscreteRep (uliftIntToIntRep (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)))) :=
  ⟨fun a => isOpen_stabilizer (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) a⟩

def localInvU (v : HeightOneSpectrum (𝓞 K.1)) :
    cohomology (galUnits.{0} (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2 →+ QZ :=
  (brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
    ((cohomologyMap (galUnitsToZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2).hom.toAddMonoidHom.comp
      (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom)

theorem localInvU_eq (v : HeightOneSpectrum (𝓞 K.1)) :
    localInvU v = (brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
      ((cohomologyMap (galUnitsToZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) 2).hom.toAddMonoidHom.comp
        (cohomologyULiftIntAddEquiv _ 2).toAddMonoidHom) :=
  rfl

variable (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

theorem localInvU_cohomologyMapAlong_gsUnitsLocalMor (v : S)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1)) ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (gsUnitsLocalMor S ιs v) 2).hom x) =
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        ((gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2 x)) := by
  refine (DFunLike.congr_fun (localInvU_eq (v : HeightOneSpectrum (𝓞 K.1))) _).trans ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  refine Eq.trans ?_ (placeInv_inr_apply _ _).symm
  refine congrArg (brauerInvZOfIsSepClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
    (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) ?_
  refine (AddMonoidHom.comp_apply _ _ _).trans ?_
  have hres : cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (embUnitsMorZ S (ιs v)) 2 = gsLocalRes S (ιs v) 2 := by
    unfold gsLocalRes gsFinFamily
    rfl
  have h := cohomologyMap_uliftInt_cohomologyMapAlong_of
    (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
    (gsUnitsLocalMor S ιs v) (galUnitsToZ _ _) (embUnitsMorZ S (ιs v)) (fun _ => rfl) 2 x
  refine h.trans ?_
  exact congrArg (fun m => m.hom (cohomologyULiftIntAddEquiv _ 2 x)) hres

theorem localInvU_cohomologyMapAlong_gsSUnitsLocalMor (v : S)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) :
    localInvU (v : HeightOneSpectrum (𝓞 K.1)) ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
      (continuous_toMonoidHom _) (gsSUnitsLocalMor S ιs v) 2).hom y) =
      placeInv (K := K) (.inr (v : HeightOneSpectrum (𝓞 K.1)))
        ((gsLocalRes S (ιs v) 2).hom (cohomologyULiftIntAddEquiv _ 2
          ((cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom y))) := by
  exact (congrArg (localInvU (v : HeightOneSpectrum (𝓞 K.1)))
    (cohomologyMapAlong_cohomologyMap_apply (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) (gsUnitsLocalMor S ιs v) 2 y).symm).trans
    (localInvU_cohomologyMapAlong_gsUnitsLocalMor S ιs v _)

theorem two_nsmul_placeInv_inl (v : InfinitePlace K.1) (y : localGaloisCohomology K 2 (.inl v)) :
    2 • placeInv (.inl v) y = 0 := by
  by_cases hc : v.IsComplex
  · have := subsingleton_cohomology_two_of_isComplex v hc
    rw [show y = 0 from Subsingleton.elim (α := cohomology (galUnitsZ v.Completion
      (AlgebraicClosure v.Completion)) 2) y 0, map_zero, smul_zero]
  · by_cases hy0 : y = 0
    · rw [hy0, map_zero, smul_zero]
    · change 2 • quadraticInvFun v.Completion (AlgebraicClosure v.Completion) y = 0
      rw [quadraticInvFun_of_ne_zero _ _ hy0, two_nsmul, QZ.mk_half_add_mk_half]

variable [Fintype S]

end Inv

end

end GroundTheory.ProfCoh
