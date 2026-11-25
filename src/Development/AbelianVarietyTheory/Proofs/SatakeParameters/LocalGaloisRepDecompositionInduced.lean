module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
open GlobalTheory.WeilDeligne Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.PstLine

section St

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V')

def stMap : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := f.rTensor (Bst P)

@[simp] theorem stMap_tmul (v : V) (b : Bst P) : stMap P f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

theorem stMap_smul {a : ↥L.1} {a' : ↥L'.1} (h : ∀ x, f (a • x) = a' • f x) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (a • x) = a' • stMap P f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [smul_tmul', stMap_tmul, h, stMap_tmul, smul_tmul']
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

variable {f ρ ρ'}

theorem stMap_stRep (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (stRep P ρ g x) = stRep P ρ' g (stMap P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [he]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem stMap_mem_Dpst (he : ∀ g x, f (ρ g x) = ρ' g (f x)) {x : V ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρ) :
    stMap P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← stMap_stRep P he, hx g hg]⟩

variable (he : ∀ g x, f (ρ g x) = ρ' g (f x))

include he

end St

section Fun

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}

structure IsMor (hL : L.1 ≤ L'.1) (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V)
    (ρ' : Representation ↥L'.1 ↥(GK K) V') : Prop where
  smul : ∀ (a : ↥L.1) x, f (a • x) = IntermediateField.inclusion hL a • f x
  equiv : ∀ g x, f (ρ g x) = ρ' g (f x)

variable {hL : L.1 ≤ L'.1} (hm : IsMor hL f ρ ρ')

end Fun

section Model

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
  {L L' : FinExt l} (hL : L.1 ≤ L'.1) (m : ℕ) (r : ↥Gw →* GL (Fin m) ↥L.1)

def incV : (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L'.1) :=
  (IntermediateField.inclusion hL).toLinearMap.compLeft (Fin m)

abbrev upRep : ↥Gw →* GL (Fin m) ↥L'.1 := mapRep (IntermediateField.inclusion hL).toRingHom r

theorem isMor_incV : IsMor hL (incV hL m) (Bw.repE L r) (Bw.repE L' (upRep hL m r)) := by
  constructor
  · intro a x
    exact funext fun i => map_mul (IntermediateField.inclusion hL) a (x i)
  · intro g x
    funext i
    exact RingHom.map_mulVec (IntermediateField.inclusion hL).toRingHom
      (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) x i

end Model

end GlobalTheory.PstLine
