module

import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
public import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
public import Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

section Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem supE_add_le (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  apply _root_.Formalism.L2.PjFree.supE_add_le <;> assumption

theorem supE_smul (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  show ‖a * P p.1 p.2‖ * _ = ‖a‖ * (‖P p.1 p.2‖ * _)
  rw [norm_mul]
  ring

theorem supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  apply _root_.Formalism.L2.PjFree.supE_ne_top <;> assumption

end Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)


open Classical in
def goodOf (σ : c.F →+* ℂ) : c.F →+* ℂ := if GoodEmb c σ then σ else (starRingEnd ℂ).comp σ

theorem norm_goodOf (σ : c.F →+* ℂ) (x : c.F) : ‖goodOf c σ x‖ = ‖σ x‖ := by
  unfold goodOf
  split_ifs <;> simp

theorem goodEmb_goodOf (σ : c.F →+* ℂ) : GoodEmb c (goodOf c σ) := by
  apply _root_.Formalism.L2.PjFree.goodEmb_goodOf <;> assumption

theorem IsNormOn.of_goodOf {C : Submodule c.F (Rul Xo c)} {σ : c.F →+* ℂ} {N : Rul Xo c → ℝ}
    (h : IsNormOn C (goodOf c σ) N) : IsNormOn C σ N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simpa only [norm_goodOf] using h1, by simpa only [norm_goodOf] using h2,
    by simpa only [norm_goodOf] using h3, by simpa only [norm_goodOf] using h4⟩

def lieFac (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFac_pos (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : 0 < lieFac Dw x a := Real.exp_pos _

def supC (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  lieFac Dw x a * supN (U σ).X (laU (U σ) a n) (rdU (U σ) f)

def SupDef : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) = 0 → f = 0

variable {Xo c U}

theorem supE_cusp_ne_top {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := Submodule.mem_iInf _ |>.mp h1 σ
  have h3 := Submodule.mem_iInf _ |>.mp h2 hσ
  exact supE_ne_top (U σ).X (laU (U σ) a n) (Submodule.mem_comap.mp h3)

theorem isNormOn_supC (x : ℝ) (h : SupDef Xo c U) {a n} (hd : Dom a n) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) :
    IsNormOn (cusp Xo c U a n) σ (supC Xo c U x σ a n) := by
  constructor
  · intro f _
    exact mul_nonneg (lieFac_pos _ _ _).le (supN_nonneg _ _ _)
  · intro f hf h0
    exact h a n hd σ hσ f hf ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne')
  · intro y f _
    unfold supC supN
    rw [map_smulₛₗ, supE_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    ring
  · intro f hf g hg
    unfold supC supN
    rw [← mul_add, map_add (f := _), ← ENNReal.toReal_add (supE_cusp_ne_top hσ hf) (supE_cusp_ne_top hσ hg)]
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ?_ (supE_add_le _ _ _ _)) (lieFac_pos _ _ _).le
    exact ENNReal.add_ne_top.mpr ⟨supE_cusp_ne_top hσ hf, supE_cusp_ne_top hσ hg⟩

variable (U)

-- Prefer the same-scalar submodule instance when elaborating the L² constructions.
attribute [local instance 2000] Submodule.module

def rdC (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n →ₛₗ[σ] FDSec (U σ).X :=
  (rdU (U σ)).comp (cusp Xo c U a n).subtype

variable {D : D7} (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)

def CuspL2 : Prop := ∀ a n, Dom a n → JMemL2 V σ (rdC U σ a n) dict mu


open Classical in
def l2C (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : JMemL2 V σ (rdC U σ a n) dict mu) (f : Rul Xo c) : ℝ :=
  if hf : f ∈ cusp Xo c U a n then
    lieFac Dw x a * l2NormAlt V σ (rdC U σ a n) dict mu h ⟨f, hf⟩ else 0

def L2DefiniteCuspForms (h : CuspL2 U σ V dict mu) : Prop :=
  ∀ a n (hd : Dom a n), L2Definite V σ (rdC U σ a n) dict mu (h a n hd)

variable {U σ V dict mu}

theorem l2C_le_supC (x : ℝ) (hσ : GoodEmb c σ) {a n} (h : JMemL2 V σ (rdC U σ a n) dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom) (hm : MuUnit V dict mu) :
    ∀ f ∈ cusp Xo c U a n, l2C U σ V dict mu x a n h f ≤ supC Xo c U x σ a n f := by
  intro f hf
  unfold l2C supC
  rw [dite_eq_left hf]
  refine mul_le_mul_of_nonneg_left ?_ (lieFac_pos Dw x a).le
  exact L2Norm_le_sup_norm (V := V) (la := laU (U σ) a n) (rd := rdC U σ a n) (dict := dict) (mu := mu) (h := h)
    (hd := hd) (hm := hm) (f := ⟨f, hf⟩) (hfin := supE_cusp_ne_top hσ hf)

theorem rdC_continuousOn (hU : IsUnf (U σ)) {a n} (hd : Dom a n) (f : cusp Xo c U a n) (k : (U σ).Comp) :
    ContinuousOn (rdC U σ a n f k) ((U σ).X k).dom := by
  obtain ⟨-, -, -, -, hsec, -⟩ := hU
  have hf : (f : Rul Xo c) ∈ sec Xo c a n := (Submodule.mem_inf.mp f.2).1
  exact (hsec a n hd f hf k).1.continuousOn

end Formalism.L2.Pj
