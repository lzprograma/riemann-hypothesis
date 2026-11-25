module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocalRep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantShift
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Topology.Algebra.MvPolynomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace Mono

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isOpen_relevant : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem eval_eq_of_aeval_eq {y : (Σ k, ι k) → Ω} {d : K → ℕ} {g g' : MRing ι}
    (hg : IsMultiHomog g d) (hg' : IsMultiHomog g' d) (he : aeval y g = aeval y g')
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) g) = eval z (map (Int.castRingHom ℂ) g') := by
  have hmem : g - g' ∈ mCoordIdeal y := by
    show mConeMap y (g - g') = 0
    rw [map_sub, ProjLine.mConeMap_eq_of_isMultiHomog y hg, ProjLine.mConeMap_eq_of_isMultiHomog y hg', he,
      sub_self]
  have h0 := hz.2 _ hmem
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

theorem smallSectionCount_le_of_injOn {P Q : ℕ → Ω → Prop} {La La' : ℕ → AddSubgroup Ω} {n : ℕ} (φ : Ω → Ω)
    (hinj : Set.InjOn φ (La n)) (hmaps : ∀ s ∈ La n, P n s → φ s ∈ La' n ∧ Q n (φ s))
    (hfin : {s : La' n | Q n (s : Ω)}.Finite) : smallSectionCount P La n ≤ smallSectionCount Q La' n := by
  unfold smallSectionCount
  have : Finite {s : La' n // Q n (s : Ω)} := hfin.to_subtype
  have hle : Nat.card {s : La n // P n (s : Ω)} ≤ Nat.card {s : La' n // Q n (s : Ω)} :=
    Nat.card_le_card_of_injective
      (fun s => ⟨⟨φ s.1, (hmaps s.1 s.1.2 s.2).1⟩, (hmaps s.1 s.1.2 s.2).2⟩)
      (fun s t hst => by
        have h1 : φ s.1 = φ t.1 := congrArg (fun u : {s : La' n // Q n (s : Ω)} => ((u.1 : La' n) : Ω)) hst
        exact Subtype.ext (Subtype.ext (hinj s.1.2 t.1.2 h1)))
  rcases Nat.eq_zero_or_pos (Nat.card {s : La n // P n (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

theorem fam_hermZpow {I : Ideal (MRing ι) → (m : ℕ) → (Fin m → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) {M : HermLine ι} (hM : IsSmoothHerm M) (a : ℕ) :
    I P (D + 1) (fun _ => Inter.hermZpow M a) = (a : ℝ) ^ (D + 1) * I P (D + 1) (fun _ => M) := by
  have hZ := Inter.isSmoothHerm_hermZpow hM (a : ℤ)
  let Lj : ℕ → Fin (D + 1) → HermLine ι := fun j i => if (i : ℕ) < j then Inter.hermZpow M a else M
  have hs : ∀ j i, IsSmoothHerm (Lj j i) := fun j i => by
    simp only [Lj]
    split_ifs
    exacts [hZ, hM]
  have step : ∀ j, j < D + 1 → I P (D + 1) (Lj (j + 1)) = a * I P (D + 1) (Lj j) := by
    intro j hj
    have e1 : Lj (j + 1) = Function.update (Lj j) ⟨j, hj⟩ (Inter.hermZpow M a) := by
      funext i
      by_cases hi : i = ⟨j, hj⟩
      · subst hi
        simp [Lj]
      · rw [Function.update_of_ne hi]
        have hij : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
        simp only [Lj]
        by_cases h1 : (i : ℕ) < j
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
    have e0 : Lj j = Function.update (Lj j) ⟨j, hj⟩ M := by
      funext i
      by_cases hi : i = ⟨j, hj⟩
      · subst hi
        simp [Lj]
      · rw [Function.update_of_ne hi]
    rw [e1, Inter.fam_update_eq_snoc hI hP (Lj j) (hs j) ⟨j, hj⟩ hZ]
    conv_rhs => rw [e0, Inter.fam_update_eq_snoc hI hP (Lj j) (hs j) ⟨j, hj⟩ hM]
    rw [Inter.fam_snoc_zpow hI hP _ (fun i => hs j _) hM (a : ℤ)]
    push_cast
    ring
  have hall : ∀ j, j ≤ D + 1 → I P (D + 1) (Lj j) = (a : ℝ) ^ j * I P (D + 1) (Lj 0) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [step j (by omega), ih (by omega), pow_succ]
      ring
  have h0 : Lj 0 = fun _ => M := by
    funext i
    simp [Lj]
  have hD : Lj (D + 1) = fun _ => Inter.hermZpow M a := by
    funext i
    simp [Lj, i.2]
  rw [← hD, hall (D + 1) le_rfl, h0]

theorem constShift_a (A : HermLine ι) (t : ℝ) : (HermLine.constShift A t).a = A.a := by
  show A.a + 0 = A.a
  exact add_zero _

theorem constShift_h (A : HermLine ι) (t : ℝ) (z : (Σ k, ι k) → ℂ) :
    (HermLine.constShift A t).h z = Real.exp (-t) * A.h z := by
  show A.h z * Real.exp (-t) = _
  ring

theorem semipos_constShift {P0 P : Ideal (MRing ι)} {A : HermLine ι} (h : IsSemipositiveRel P0 P A) (t : ℝ) :
    IsSemipositiveRel P0 P (HermLine.constShift A t) := by
  have hh : (HermLine.constShift A t).h = fun z => Real.exp (-t) * A.h z := funext (constShift_h A t)
  refine ⟨?_, fun z hz w hw => ?_⟩
  · unfold IsSmoothHerm
    rw [hh]
    exact contDiffOn_const.mul h.1
  · have hev : (fun z => Real.log ((HermLine.constShift A t).h z)) =ᶠ[𝓝 z]
        fun z => -t + Real.log (A.h z) := by
      filter_upwards [isOpen_relevant.mem_nhds hz.1] with z' hz'
      rw [constShift_h, Real.log_mul (Real.exp_pos _).ne' (A.pos z' hz').ne', Real.log_exp]
    have h2 : fderiv ℝ (fderiv ℝ fun z => Real.log ((HermLine.constShift A t).h z)) z =
        fderiv ℝ (fderiv ℝ fun z => Real.log (A.h z)) z := by
      rw [hev.fderiv.fderiv_eq]
      congr 1
      funext x
      exact fderiv_const_add _
    unfold leviForm
    rw [h2]
    exact h.2 z hz w hw

theorem conj_constShift {A : HermLine ι} (h : IsConjInvariantH A) (t : ℝ) :
    IsConjInvariantH (HermLine.constShift A t) := fun z => by
  rw [constShift_h, constShift_h, h z]

theorem smallGen_constShift {P0 : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {D : ℕ} {L : HermLine ι}
    (h : IsSmallGeneratedDatum P0 y D L) {t : ℝ} (ht : t ≤ 0) :
    IsSmallGeneratedDatum P0 y D (HermLine.constShift L t) := by
  obtain ⟨q, w, hw, hgen, hsmall⟩ := h.gen
  refine ⟨h.normalForm_baseLattice_le_dualSpan_sup_line, semipos_constShift h.semipos t, ?_, ⟨q, w, ?_, ?_, fun j => ?_⟩⟩
  · rw [constShift_a]
    exact h.deg_pos
  · rw [constShift_a]
    exact hw
  · rw [constShift_a]
    exact hgen
  · intro dg dh g hh z hg hhh hd he hz
    rw [constShift_a] at hd
    have h1 := hsmall j dg dh g hh z hg hhh hd he hz
    rw [constShift_h, pow_one]
    rw [pow_one] at h1
    have hL := (L.pos z hz.1).le
    have he1 : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    nlinarith

theorem chartLat_le_nm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h1 := hs c hc
  exact isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, h1⟩)

end Mono


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
