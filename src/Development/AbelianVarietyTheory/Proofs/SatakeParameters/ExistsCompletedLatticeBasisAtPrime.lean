module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAEMulMem

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.LatLocBasis

noncomputable abbrev locRing {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Subalgebra (𝓞 E) E :=
  Localization.subalgebra.ofField E P.asIdeal.primeCompl P.asIdeal.primeCompl_le_nonZeroDivisors

theorem exists_gens {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ b : Fin n → Fin n → E, (∀ i, b i ∈ Submodule.span (locRing P) (L : Set (Fin n → E))) ∧
      ∀ x ∈ L, ∃ c : Fin n → locRing P, ∀ a, x a = ∑ i, (c i : E) * b i a := by
  have : IsLocalization.AtPrime (locRing P) P.asIdeal :=
    Localization.subalgebra.isLocalization_ofField E _ _
  have : IsDiscreteValuationRing (locRing P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot _
  have : IsFractionRing (locRing P) E := Localization.subalgebra.isFractionRing_ofField E _ _
  let M := Submodule.span (locRing P) (L : Set (Fin n → E))
  have hM : Submodule.IsLattice E M := Submodule.IsLattice.of_fg E (by
    obtain ⟨s, rfl⟩ := hfg
    exact ⟨s, (Submodule.span_span_of_tower (𝓞 E) (locRing P) _).symm⟩)
  have : Submodule.IsFullLattice E M :=
    { hM with span_eq_top := by rw [Submodule.span_span_of_tower, hsp] }
  have : Module.Finite (locRing P) M := Submodule.IsLattice.finite E M
  have : Module.Free (locRing P) M := Submodule.IsLattice.free E M
  have hr : Module.finrank (locRing P) M = n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq E M).trans (Module.finrank_fintype_fun_eq_card E))
  let b := Module.finBasisOfFinrankEq (locRing P) M hr
  refine ⟨fun i => b i, fun i => (b i).2, fun x hx => ?_⟩
  refine ⟨b.repr ⟨x, Submodule.subset_span hx⟩, fun a => ?_⟩
  have h := congrArg (fun v : M => (v : Fin n → E) a) (b.sum_repr ⟨x, Submodule.subset_span hx⟩)
  simp only [Submodule.coe_sum, Finset.sum_apply] at h
  exact h.symm

theorem idem_mul_loc_mem {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsIdemAt e P) {t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F} (ht : t ∈ intAf D.host.F) (c : locRing P) :
    finPart D e * (t ⊗ₜ[D.host.F] (c : D.host.E)) ∈ intAE D := by
  obtain ⟨a, s, hs, hc⟩ := c.2
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ P.asIdeal.zero_mem)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hn
    exact hs ((h.2 s hs0).2 hn)
  have h2 : (t ⊗ₜ[D.host.F] (a : D.host.E)) ∈ intAE D := AddSubgroup.subset_closure ⟨t, ht, a, rfl⟩
  have h3 := GlobalTheory.IntegralAdeleProducts.intAE_mul_mem (F := D.host.F) (E := D.host.E) h1 h2
  have h4 : finPart D (incA D ((s : D.host.E)⁻¹)) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((s : D.host.E)⁻¹) := rfl
  rw [RingHom.map_mul, h4, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm _ (a : D.host.E)] at h3
  rw [hc]
  exact h3

theorem one_mem_intAf (F : Type) [Field F] [NumberField F] : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ intAf F :=
  fun v => by rw [map_one]; exact one_mem _

theorem idem_mul_span_mem {D : D7} (V : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsIdemAt e P) {x : Fin V.rank → D.host.E}
    (hx : x ∈ Submodule.span (locRing P) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) :
    (fun a => finPart D e * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a)) ∈ LamHat V := by
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, h.1.1]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have h1 : finPart D e ∈ intAE D := by
      have := idem_mul_loc_mem h (one_mem_intAf _) 1
      rwa [OneMemClass.coe_one, ← Algebra.TensorProduct.one_def, mul_one] at this
    refine GlobalTheory.LatDual.smul_mem_lamHat V _ h1 _ ?_
    rw [GlobalTheory.LatDual.lamHat_eq_hat]
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩
  | zero =>
    simp only [Pi.zero_apply, TensorProduct.tmul_zero, mul_zero]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [Pi.add_apply, TensorProduct.tmul_add, mul_add]
    exact add_mem hu hw
  | smul c u _ hu =>
    have := GlobalTheory.LatDual.smul_mem_lamHat V _ (idem_mul_loc_mem h (one_mem_intAf _) c) _ hu
    convert this using 2 with a
    rw [mul_mul_mul_comm, hee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl



theorem exists_loc_basis : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), IsIdemAt e P → ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), (∀ z, IntVec z → (fun a => finPart D e * B.mulVec z a) ∈ LamHat V) ∧ ∀ y ∈ LamHat V, ∃ z, IntVec z ∧ (fun a => finPart D e * y a) = fun a => finPart D e * B.mulVec z a := by
  intro D V P e h
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, h.1.1]
  obtain ⟨-, -, hfg, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨b, hb, hc⟩ := exists_gens P (GlobalTheory.Member.latC V) hfg hspan
  have h1 : finPart D e ∈ intAE D := by
    have := idem_mul_loc_mem h (one_mem_intAf _) 1
    rwa [OneMemClass.coe_one, ← Algebra.TensorProduct.one_def, mul_one] at this
  refine ⟨Matrix.of fun a i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] b i a, fun z hz => ?_, fun y hy => ?_⟩
  · have := sum_mem (S := LamHat V) (t := Finset.univ) fun i _ =>
      GlobalTheory.LatDual.smul_mem_lamHat V _ (hz i) _ (idem_mul_span_mem V h (hb i))
    convert this using 1
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [GlobalTheory.LatDual.lamHat_eq_hat] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      obtain ⟨c, hc⟩ := hc x hx
      refine ⟨fun i => finPart D e * (t ⊗ₜ[D.host.F] (c i : D.host.E)), fun i => idem_mul_loc_mem h ht _, ?_⟩
      funext a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
      rw [hc a, TensorProduct.tmul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm _ (finPart D e), ← mul_assoc, hee, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_comm (b i a)]
    | zero => exact ⟨0, fun _ => zero_mem _, by rw [Matrix.mulVec_zero]⟩
    | add u w _ _ hu hw =>
      obtain ⟨z, hz, hu⟩ := hu
      obtain ⟨z', hz', hw⟩ := hw
      refine ⟨z + z', fun i => add_mem (hz i) (hz' i), funext fun a => ?_⟩
      rw [Matrix.mulVec_add, Pi.add_apply, Pi.add_apply, mul_add, mul_add, congrFun hu a, congrFun hw a]
    | neg u _ hu =>
      obtain ⟨z, hz, hu⟩ := hu
      refine ⟨-z, fun i => neg_mem (hz i), funext fun a => ?_⟩
      rw [Matrix.mulVec_neg, Pi.neg_apply, Pi.neg_apply, mul_neg, mul_neg, congrFun hu a]

end GlobalTheory.LatLocBasis
