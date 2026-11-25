module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise

namespace GlobalTheory.Fam

variable {D : D7}

def UnitRatio (S : ℕ → Prop) (x y : ℂ) : Prop :=
  y ≠ 0 ∧ ∃ n : ℕ, 0 < n ∧ ∃ r : ℚ, r ≠ 0 ∧ (x / y) ^ n = (r : ℂ) ∧ ∀ p : ℕ, p.Prime → padicValRat p r ≠ 0 → S p

structure Base (c : Comm D) where
  Λ : ∀ j, GlobalTheory.FinPl.Lat (c.V j)
  β : ∀ j, GL (Fin (c.V j).rank) (Lev.EAf D)
  b : ∀ j, GA D (c.V j)

  ΛT : GlobalTheory.FinPl.Lat c.T
  βT : GL (Fin c.T.rank) (Lev.EAf D)
  bT : GA D c.T
  LT : GlobalTheory.FinPl.Lat c.T
  Pg : Finset (Formalism.L2.DIV.Pl D.host.E)
  P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ

variable {c : Comm D}

section Off

open GlobalTheory.FinPl

structure Off (B : Base c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where
  p : ι → SplitPt D k

  I : List ι

  q : Unif k

  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1

  β : ∀ j i, Frame (p i) (c.X j) (Fin (c.X j).rank)

  Q : ∀ j, ι → Pair k (Fin (c.X j).rank)

  β₀ : ∀ j ρ h i, Frame (p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)

  L : ∀ j, Lat (c.V j)

  M : ∀ j ρ h, Lat (c.bes j ρ h).V₀

  cT : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ

  cG : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ

  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E

  ζ₀ : Fin c.Lz.rank → D.host.E

  γ : ∀ i, Frame (p i) c.T (Fin c.T.rank)

  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (c.X n) (Fin c.T.rank ⊕ Fin 1)

variable {B : Base c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : Off B k ι)

end Off

section AtLevel

open GlobalTheory.LocMod

variable {B : Base c} {τ : ∀ j h, Matrix (Fin (c.bes j 0 h).L.rank) (Fin c.Lz.rank) D.host.E}

end AtLevel



end GlobalTheory.Fam

end
