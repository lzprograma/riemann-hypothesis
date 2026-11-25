module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct

namespace GlobalTheory.CharUnramVal

theorem locK_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt Q) (k : Lˣ) (m : ℤ) (hk : Q.valuation L (k : L) = WithZero.exp (-m)) :
    χ.locK Q k = χ.val Q ^ m := by
  have h1 : Valued.v ((atFin Q k : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-m) :=
    (GlobalTheory.CharLocProd.val_algebraMap Q (k : L)).trans hk
  have h2 : Valued.v ((atFin Q (unif Q) : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec Q
  have h3 : IsUnitAt Q (atFin Q k * atFin Q (unif Q) ^ (-m)) := by
    show Valued.v _ = _
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h1, h2, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h4 := hu _ h3
  rw [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at h4
  exact h4

theorem char_eq_prod_val_zpow : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (m : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ Q ∈ S, χ.UnrAt Q ∧ Valued.v (ι (finPart D (x : AE D)) Q) = WithZero.exp (-m Q)) → (∀ Q, Q ∉ S → ι (finPart D (x : AE D)) Q = 1) → ((c x : Circle) : ℂ) = ((∏ Q ∈ S, χ.val Q ^ m Q : ℂˣ) : ℂ) := by
  classical
  intro D ι h1 h2 h3 c χ hc x hx S m hS hoff
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h3 c χ hc
  obtain ⟨S', k₀, -, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have hx0 : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (x : AE D)) P ≠ 0 := by
    intro P h
    by_cases hP : P ∈ S
    · have := (hS P hP).2
      rw [h, map_zero] at this
      exact WithZero.exp_ne_zero this.symm
    · exact zero_ne_one (h.symm.trans (hoff P hP))
  choose k hk using fun P => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hx0 P)
  have key := hprod x hx (S ∪ S') (fun P => if P ∈ S then k P else 1) (fun P _ => by
    by_cases hP : P ∈ S
    · simp only [ite_eq_left hP]
      exact ⟨(hk P).1, (hk P).2.1⟩
    · simp only [ite_eq_right hP, hoff P hP, Units.val_one, map_one, sub_self, map_zero, zero_le, and_self])
    (fun P hP => hS' P fun h => hP (Finset.mem_union_right _ h))
  rw [key, Units.coe_prod, ← Finset.prod_subset (Finset.subset_union_left (s₁ := S) (s₂ := S'))]
  · refine Finset.prod_congr rfl fun P hP => ?_
    simp only [ite_eq_left hP]
    rw [locK_eq_val_zpow χ P (hS P hP).1 (k P) (m P) ((hk P).1.symm.trans (hS P hP).2)]
  · intro P _ hP
    simp only [ite_eq_right hP, map_one, Units.val_one]

end GlobalTheory.CharUnramVal
