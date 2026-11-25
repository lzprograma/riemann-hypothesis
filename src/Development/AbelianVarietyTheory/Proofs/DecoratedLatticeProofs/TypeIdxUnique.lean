module

public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FamTraceChiCol


open Classical in
def colLam {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : ℂ :=
  if h : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal then
    Formalism.L2.Forms.lamJ (T.gl.psi0 h.choose v h.choose_spec) (T.gl.chiB h.choose v h.choose_spec) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
        (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g)))
  else 1

theorem type_idx_unique {D : D7} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)} {j j' : Fin 2}
    (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal) : j' = j := by
  by_contra hne
  have hg : D.host.g j' ≠ D.host.g j := by
    intro e
    rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;> rcases Fin.exists_fin_two.mp ⟨j', rfl⟩ with hj' | hj' <;>
      subst hj hj' <;> first | exact hne rfl | exact D.host.g_ne e | exact D.host.g_ne e.symm
  have hc : Nat.Coprime (D.host.g j') (D.host.g j) := (Nat.coprime_primes (D.host.g_prime j') (D.host.g_prime j)).2 hg
  obtain ⟨a, b, hab⟩ : IsCoprime (D.host.g j' : ℤ) (D.host.g j : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  have h1 : (1 : 𝓞 D.host.F) ∈ v.asIdeal := by
    have e : ((a * (D.host.g j' : ℤ) + b * (D.host.g j : ℤ) : ℤ) : 𝓞 D.host.F) = 1 := by rw [hab]; simp
    rw [← e]
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h') (v.asIdeal.mul_mem_left _ h)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem colLam_eq {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)}
    (j : Fin 2) (h : (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal)
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    colLam T v g = Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
      (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
  have hex : ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal := ⟨j, h⟩
  unfold colLam
  rw [dite_eq_left hex]
  have key : ∀ (j' : Fin 2) (h' : (D.host.g j' : 𝓞 D.host.F) ∈ v.asIdeal), j' = j →
      Formalism.L2.Forms.lamJ (T.gl.psi0 j' v h') (T.gl.chiB j' v h') D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j' v h' (T.glev0.fr j' v h') (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) =
      Formalism.L2.Forms.lamJ (T.gl.psi0 j v h) (T.gl.chiB j v h) D.R.k D.R.t 0 D.R.k
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat j v h (T.glev0.fr j v h) (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) := by
    rintro j' h' rfl; rfl
  exact key _ _ (type_idx_unique h hex.choose_spec)

end GlobalTheory.FamTraceChiCol

end
