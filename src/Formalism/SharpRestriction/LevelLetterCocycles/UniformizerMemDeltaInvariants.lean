module

import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Mathlib.Tactic.Lemma

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

section Setup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem qp_mem (hπ : W.π₀ ∈ W.AΔ) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
  show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
  exact add_mem hπ (Subalgebra.natCast_mem _ _)

def QhP (i : ZMod n) (h : ℕ) : Submodule O (W.DD T) :=
  (PhiPullΔ W T i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))

theorem uniformizer_mem_delta_invariants : W.π₀ ∈ W.AΔ := by
  apply _root_.Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.pi0_mem_ADelta <;> assumption

end Setup

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def NinQbP [NeZero n] : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      x ∈ (PhiPullΔ W T₂ i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
