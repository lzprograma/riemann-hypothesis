module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)

namespace GlobalTheory.WeilSchrodinger

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem symp_transpose (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ JB JA xᵀ yᵀ = GlobalTheory.WeilM.symp c ξ JA JB x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable [Invertible (2 : R)]

def transD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans d.e
  form w w' := by
    rw [← symp_transpose c ξ JB JA w w', d.form]
    rfl

variable {c}

theorem transD_e {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α β E) : (transD c d).e xᵀ = d.e x := by
  simp [transD]

theorem transD_rho {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (ψ : AddChar R ℂ) (w : Matrix β α E) :
    (transD c d).rho ψ w = d.rho ψ wᵀ := by
  simp [GlobalTheory.WeilM.Darboux.rho, transD]

variable [TopologicalSpace R] [TopologicalSpace E] {C : GlobalTheory.WeilM.TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ] {d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ}
  {om : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB →* Module.End ℂ ((κ → R) → ℂ)}

theorem isUSplitting_inr (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inr _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inr _ _) (continuous_const.prodMk continuous_id)⟩
  have := h.impl (1, g) w φ hφ
  simpa [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB] using this

theorem isUSplitting_inl (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ (transD c d) (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inl _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inl _ _) (continuous_id.prodMk continuous_const)⟩
  have := h.impl (g, 1) wᵀ φ hφ
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, transD_rho]
  convert this using 2
  simp [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, Matrix.transpose_mul]

end Gen

section Theta

variable (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)]

def thetaTr {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) : W → ℂ :=
  fun w => GlobalTheory.WeilM.thetaSum F (d.rho ψ w Φ)

end Theta

section Transport

def IsTransport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {ξ : AE D}
    {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E} {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ))
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)) :
    Prop :=
  ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) (g : GA D S) (h : GA D T),
    mt T h = a.1.1 → mt S g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om (a, b) Φ ∈ GlobalTheory.WeilM.schA D.host.F κ ∧
      thetaTr D.host.F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr D.host.F co ψ Φ)

end Transport

end GlobalTheory.WeilSchrodinger

end
