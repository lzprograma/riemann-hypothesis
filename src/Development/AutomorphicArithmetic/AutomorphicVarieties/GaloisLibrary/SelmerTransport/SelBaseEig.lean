module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelBase
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

noncomputable section

open ReciprocityTheory.Gal

namespace UpperTheory.V.Base

section Cohomology

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
  {O M' : Type} [CommRing O] [Algebra R O] [AddCommGroup M'] [Module O M']
  [Module R M'] [IsScalarTower R O M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M']
  (ρ : Representation R G M) (ρ' : Representation O G M') (j : M →ₗ[R] M')
  (hj : ∀ g m, j (ρ g m) = ρ' g (j m))
  (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟)

theorem selMap_selRep (g : G) (x : LocSel ρ U 𝒟) :
    selMap ρ ρ' j hj U 𝒟 (selRep ρ U h𝒟 g x) =
      selRep ρ' U h𝒟 g (selMap ρ ρ' j hj U 𝒟 x) := by
  apply Subtype.ext
  change h1Map ρ ρ' j hj U (conjU ρ U g x.1) =
    conjU ρ' U g (h1Map ρ ρ' j hj U x.1)
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
  rw [← hz]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun w => hj _ _))

/-- The coefficient map restricted to a character subspace of locally trivial classes. -/
def selEigMap (W : Subgroup G) (ψ : W →* Rˣ) :
    selEig ρ U h𝒟 W ψ →ₗ[R]
      selEig ρ' U h𝒟 W ((Units.map (algebraMap R O).toMonoidHom).comp ψ) where
  toFun x := ⟨selMap ρ ρ' j hj U 𝒟 x, by
    have hx := x.2
    rw [mem_eig] at hx ⊢
    change ∀ w : W, selRep ρ U h𝒟 w x.1 = (ψ w : R) • x.1 at hx
    intro w
    change selRep ρ' U h𝒟 w (selMap ρ ρ' j hj U 𝒟 x.1) =
      algebraMap R O (ψ w : R) • selMap ρ ρ' j hj U 𝒟 x.1
    rw [← selMap_selRep, hx w, map_smul, algebraMap_smul]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- Finite free coefficient extension commutes with the Selmer character subspace. -/
theorem isBaseChange_selEigMap [Module.Free R O] [Module.Finite R O]
    (hb : IsBaseChange O j) (W : Subgroup G) (ψ : W →* Rˣ) :
    IsBaseChange O (selEigMap ρ ρ' j hj U h𝒟 W ψ) := by
  let b := Module.Free.chooseBasis R O
  have hS := isBaseChange_selMap ρ ρ' j hj U hb 𝒟
  apply isBaseChange_restrict b hS _ _ _ _ (fun _ => rfl)
  intro x
  simp only [selEig, mem_eig]
  rw [forall_comm]
  exact forall_congr' fun w => coordSum_eigenvector_iff b hS
    (selRep ρ U h𝒟 w) (selRep ρ' U h𝒟 w)
    (selMap_selRep ρ ρ' j hj U h𝒟 w) (ψ w : R) x

/-- The coefficient map restricted to an eigenspace of one conjugation operator. -/
def selEigenspaceMap (g : G) (s : R) :
    Module.End.eigenspace (selRep ρ U h𝒟 g) s →ₗ[R]
      Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s) where
  toFun x := ⟨selMap ρ ρ' j hj U 𝒟 x, by
    have hx := x.2
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← selMap_selRep, hx, map_smul, algebraMap_smul]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem isBaseChange_selEigenspaceMap [Module.Free R O] [Module.Finite R O]
    (hb : IsBaseChange O j) (g : G) (s : R) :
    IsBaseChange O (selEigenspaceMap ρ ρ' j hj U h𝒟 g s) := by
  let b := Module.Free.chooseBasis R O
  have hS := isBaseChange_selMap ρ ρ' j hj U hb 𝒟
  apply isBaseChange_restrict b hS _ _ _ _ (fun _ => rfl)
  intro x
  simp only [Module.End.mem_eigenspace_iff]
  exact coordSum_eigenvector_iff b hS (selRep ρ U h𝒟 g) (selRep ρ' U h𝒟 g)
    (selMap_selRep ρ ρ' j hj U h𝒟 g) s x

end Cohomology

end UpperTheory.V.Base

open UpperTheory.V.Base

theorem UpperTheory.V.Base.selBaseEig :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (O M' : Type) [CommRing O] [Algebra R O] [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] [Module.Free R O]
      [Module.Finite R O] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M'] [TopologicalSpace M']
      [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M'] (ρ' : Representation O G M') (j : M →ₗ[R] M'),
      IsBaseChange O j → (∀ g m, j (ρ g m) = ρ' g (j m)) → ∀ (U : Subgroup G) [U.Normal] (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      (∀ (W : Subgroup G) (ψ : W →* Rˣ), Module.length O (selEig ρ' U h𝒟 W ((Units.map (algebraMap R O).toMonoidHom).comp ψ)) =
        Module.length R (selEig ρ U h𝒟 W ψ) * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O))) ∧
      ∀ (g : G) (s : R), Module.length O (Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s)) =
        Module.length R (Module.End.eigenspace (selRep ρ U h𝒟 g) s) * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ O M' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' j hj hu U _ 𝒟 h𝒟
  constructor
  · intro W ψ
    exact length_of_isBaseChange (isBaseChange_selEigMap ρ ρ' j hu U h𝒟 hj W ψ)
  · intro g s
    exact length_of_isBaseChange (isBaseChange_selEigenspaceMap ρ ρ' j hu U h𝒟 hj g s)
