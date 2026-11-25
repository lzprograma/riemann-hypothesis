module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IndepDomK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbKey
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ShiftCoordinatesColumn
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsNeZeroInFrameW1ColumnI0
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.InFrameW1EmSEqOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.UnipotentBlockCornerEmbedded
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

/-! # SplitOrInertKStatement: Consolidated global theta-kernel definitions and proofs (SplitOrInertKStatement). -/
@[expose] public section

noncomputable section
open Finset (sum_eq_single)

section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
open Matrix (fromBlocks fromBlocks_multiply toBlocks_fromBlocks₂₁ single_apply transpose_apply submatrix_apply)
open GlobalTheory.EisBL.DoubledParabolic (inFrame_mul inFrame_one)
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
abbrev _root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK :=
  GlobalTheory.KFinLoc.split_or_inert_k

namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
def eA_k : AE F E := (((R.ε : ℤ) : E) : E) |> inclR (F := F) (E := E) (AF F)
def elt_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) : d.G :=
  if h : ∃ x : d.G, inFrame d.b x = M then h.choose else 1
def uA_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)
def bMat_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  fromBlocks 1 β 0 1
def sB_k (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(eA_k R * cA σ (b j))))
def aB_k (δ : E) (a : AF F) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ (a • inclR (F := F) (E :=
  E) (AF F) δ)
structure Hyp_k (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a', inFrame d.b (uM u) = fromBlocks (uA_k L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (AF F)
        a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (AF F) b)
  cf : ∀ c, ∃ A', inFrame d.b (cM c) = fromBlocks (uA_k L c.1) (aB_k L δ c.2) 0 A'
  δ0 : δ ≠ 0
def sM_k (b : Fin L.n → AE F E) : d.G := elt_k (bMat_k (sB_k R L b))
def pb_k (β : nA σ d.Y d.b) : Fin L.n → AE F E := fun j => β.1 L.i₀ (L.em j)
def pa_k (δ : E) (β : nA σ d.Y d.b) : AF F := ellA δ (β.1 L.i₀ L.i₀)
def eisensteinSecondTerm (Φ : d.G → ℂ) (g : d.G) : ℂ := ∑' q : {q : Cs_k d
  // ¬ FirstOrbit L (rep_k
  q)}, Φ (rep_k q.1 * g)
end PositivityTheory.SiegelWeilFormula.Act.C5

section
open scoped ENNReal
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
def th_k (T : nF σ d.Y d.b) (β : nA σ d.Y d.b) : ℂ := d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 *
  β.1))))
def th'_k (T' : nF σ L.Y L.b) (β : nA σ L.Y L.b) : ℂ :=
  d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1))))
theorem second_orbit_section_integral {f : d.G → ℂ} {s₁ z : ℂ} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
  {T : nF σ d.Y d.b}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : Cs_k d,
      Integrable (kq_k L f s₁ z nb T uM
      (rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : Cs_k d => ∫ p,
      ‖kq_k L f s₁ z nb T uM
      (rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x =
        ∫ p, eisensteinSecondTerm L (phz_k d f s₁ z) (nb p.2 * (uM p.1 *
          x)) * th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) ∧
      ∫⁻ p,
        ∑' q : {q : Cs_k d // ¬
        FirstOrbit L (rep_k
        q)},
        ‖phz_k d f s₁ z
        (rep_k q.1 * (nb p.2 * (uM p.1 * x))) * th_k T p.2‖ₑ
        ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) < ⊤ := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (Cs_k d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  let g : {q : Cs_k d // ¬
    FirstOrbit L (rep_k q)}
    → (Fin L.n → AE F E) × nA σ d.Y d.b → ℂ :=
    fun q => kq_k L f s₁ z nb T uM
      (rep_k q.1) x
  have hgi : ∀ q, Integrable (g q) μ := fun q => hi q.1
  have hgs : Summable fun q => ∫ p, ‖g q p‖ ∂μ := hs.subtype _
  have htm : ∀ q : {q : Cs_k d // ¬
    FirstOrbit L (rep_k q)},
    tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤
    (rep_k q.1) x = ∫ p, g q p ∂μ := by
    intro q
    rw [hμ, integral_prod _ (hgi q)]
    rfl
  constructor
  · unfold secondOrbitSection
    simp_rw [htm]
    rw [(hasSum_integral_of_summable_integral_norm hgi hgs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [g, kq_k, eisensteinSecondTerm, th_k]
    rw [tsum_mul_right]
  · have hm : ∀ q, AEMeasurable (fun p => ‖g q p‖ₑ) μ := fun q => (hgi q).aemeasurable.eNorm
    have e1 : ∫⁻ p,
      ∑' q : {q : Cs_k d // ¬
      FirstOrbit L (rep_k
      q)},
      ‖phz_k d f s₁ z (rep_k
      q.1 * (nb p.2 * (uM p.1 * x))) * th_k T p.2‖ₑ ∂μ =
        ∑' q, ENNReal.ofReal (∫ p, ‖g q p‖ ∂μ) := by
      rw [show (fun p => ∑' q : {q : Cs_k d // ¬
        FirstOrbit L (rep_k
        q)},
          ‖phz_k d f s₁ z
            (rep_k q.1 * (nb p.2 * (uM p.1 * x))) * th_k T p.2‖ₑ) = fun p
            => ∑' q, ‖g q p‖ₑ from rfl,
        lintegral_tsum hm]
      exact tsum_congr fun q => (ofReal_integral_norm_eq_lintegral_eNorm (hgi q)).symm
    rw [e1, ← ENNReal.ofReal_tsum_of_nonneg (fun q => integral_nonneg fun p => norm_nonneg _) hgs]
    exact ENNReal.ofReal_lt_top
end PositivityTheory.SiegelWeilFormula.Act.C5
end

section
set_option linter.unusedSectionVars false
open PositivityTheory.SiegelWeilFormula.Act.C5 PositivityTheory.SiegelWeilFormula.Act.C4
  PositivityTheory.SiegelWeilFormula.Act.C4.Bq
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {d : SD_k σ} {L : LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
variable (L) in
structure Hyp_k (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a',
    inFrame d.b (uM u) = fromBlocks (C5.uA_k L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (AF F)
        a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (AF F) b)
  cf : ∀ c, ∃ A',
    inFrame d.b (cM c) = fromBlocks (C5.uA_k L c.1)
    (C5.aB_k L δ c.2) 0 A'
  δ0 : δ ≠ 0
variable (L) in
abbrev Cr_k : Type := {c : (Fin L.n → AE F E) × AF F // c.1 ∈ L.ratV ∧ c.2 ∈ (algebraMap F (AF F)).range}
variable (L) in
def Fix_k (x : d.G) : Prop :=
  ∀ k, inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)
theorem fix_mul_k {x y : d.G} (hx : Fix_k L x) (hy : Fix_k L y) : Fix_k L (x * y) := by
  intro k
  rw [inFrame_mul, Matrix.mul_apply, sum_eq_single (Sum.inl L.i₀)]
  · rw [hy, Matrix.one_apply_eq, mul_one]; exact hx k
  · intro j _ hj; rw [hy j, Matrix.one_apply_ne hj, mul_zero]
  · simp
theorem fix_inv_k {x : d.G} (hx : Fix_k L x) : Fix_k L x⁻¹ := by
  intro k
  have h1 := congrFun (congrFun (GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul d.b x) k) (Sum.inl L.i₀)
  rw [Matrix.mul_apply, sum_eq_single (Sum.inl L.i₀)] at h1
  · rw [hx, Matrix.one_apply_eq, mul_one] at h1; exact h1
  · intro j _ hj; rw [hx j, Matrix.one_apply_ne hj, mul_zero]
  · simp
theorem fix_j_k (g : G2 σ L.Y) : Fix_k L (L.j g) := by
  intro k
  exact (L.j_out g (Sum.inl L.i₀) (by simp) k).2
theorem first_orbit_parabolic_left {p g : d.G} (hp : p ∈ par2 σ d.Y) :
  FirstOrbit L (p * g) ↔
  FirstOrbit L g := by
  constructor
  · intro h1
    have := C4.Bq.inStabilizer_parabolic_mul L ((par2 σ d.Y).inv_mem hp)
      h1
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  · exact C4.Bq.inStabilizer_parabolic_mul L hp
theorem not_first_orbit_weyl (h : Hyp_k L nb uM nb' w₁ cM δ) {g : d.G} (hg : Fix_k L g) : ¬
  FirstOrbit L (w₁ * g) := by
  intro hS
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  have h1 := hS L.i₀
  rw [inFrame_mul, Matrix.mul_apply, sum_eq_single (Sum.inl L.i₀)] at h1
  · rw [hg, Matrix.one_apply_eq, mul_one, hW] at h1
    simp at h1
    exact hb (kfour.inclR_injective (F := F) (by rw [h1, map_zero]))
  · intro j _ hj; rw [hg j, Matrix.one_apply_ne hj, mul_zero]
  · simp
theorem out_mk_k (d : SD_k σ) (γ : rat2 σ d.Y) :
    ∃ p ∈ par2 σ d.Y,
      p ∈ rat2 σ d.Y ∧ rep_k (Quotient.mk _ γ :
      Cs_k d) = p * γ.1 := C4.Bq.rep_mk_k γ
theorem mk_eq_mk_k (d : SD_k σ) {γ γ' : rat2 σ d.Y} :
    (Quotient.mk _ γ : Cs_k d) = Quotient.mk _ γ' ↔ γ'.1 * γ.1⁻¹ ∈ par2 σ
      d.Y := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp
theorem rep_mem_k (d : SD_k σ) (q : Cs_k d) :
  rep_k q ∈ rat2 σ d.Y := (Quotient.out q).2
theorem mk_rep_k (d : SD_k σ) (q : Cs_k d) : (Quotient.mk _
  ⟨rep_k q,
  rep_mem_k d q⟩ : Cs_k d) = q := Quotient.out_eq q
theorem weyl_commutes_embedding (h : Hyp_k L nb uM nb' w₁ cM δ) (g : G2 σ L.Y) : w₁ * L.j g = L.j g * w₁ := by
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  apply kunf.inFrame_injective d.b
  rw [inFrame_mul, inFrame_mul]
  set W := inFrame d.b w₁
  set J := inFrame d.b (L.j g)
  have hJ := C4.Bq.pad_j_k L g
  let P : Fin d.n ⊕ Fin d.n → Prop := fun l => l = Sum.inl L.i₀ ∨ l = Sum.inr L.i₀
  have hWo : ∀ r c, ¬ (P r ∧ P c) → (W - 1) r c = 0 := by
    intro r c hrc
    rw [Matrix.sub_apply, hW]
    simp only [P, not_and_or] at hrc
    rcases hrc with hr | hr <;> push Not at hr <;>
      simp [Matrix.one_apply, Ne.symm hr.1, Ne.symm hr.2]
  have hJo : ∀ r c, (P r ∨ P c) → (J - 1) r c = 0 := by
    intro r c hrc
    rw [Matrix.sub_apply, sub_eq_zero]
    rcases hrc with (h | h) | (h | h)
    · exact hJ r c (Or.inl h)
    · exact hJ r c (Or.inr (Or.inl h))
    · exact hJ r c (Or.inr (Or.inr (Or.inl h)))
    · exact hJ r c (Or.inr (Or.inr (Or.inr h)))
  have e1 : (W - 1) * (J - 1) = 0 :=
    mul_eq_zero_of_supp P (fun r l hl => hWo r l fun h => hl h.2) (fun l c hl => hJo l c (Or.inl hl))
  have e2 : (J - 1) * (W - 1) = 0 :=
    mul_eq_zero_of_supp (fun l => ¬ P l) (fun r l hl => hJo r l (Or.inr (not_not.1 hl))) (fun l c hl => hWo l c fun h =>
      hl h.1)
  have eW : W = 1 + (W - 1) := by abel
  have eJ : J = 1 + (J - 1) := by abel
  rw [eW, eJ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e1, e2]
  abel
theorem uA_neg_mul_k (u : Fin L.n → AE F E) : C5.uA_k L (-u) *
  C5.uA_k L u = 1 := by
  have := C1.Au_mul_k L (-u) u
  simp only [neg_add_cancel] at this
  rw [show C5.uA_k L (-u) *
    C5.uA_k L u = C1.Au_k L
    (-u) * C1.Au_k L u from rfl, this]
  simp [C1.Au_k]
theorem cM_frame_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    inFrame d.b (cM c) = fromBlocks (C5.uA_k L c.1)
      (C5.aB_k L δ c.2) 0
      ((C5.uA_k L (-c.1))ᵀ.map (cA σ)) := by
  obtain ⟨A', hA'⟩ := h.cf c
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have h2 := kunf.frame_eq hε (cM c)
  rw [hA'] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  have h1 :=
    (Matrix.fromBlocks_inj.1 h2).2.1
  have h1' := mul_eq_one_comm.1 h1
  have hinv : (C5.uA_k L c.1)ᵀ *
    (C5.uA_k L (-c.1))ᵀ = 1 :=
    by rw [← Matrix.transpose_mul, uA_neg_mul_k, Matrix.transpose_one]
  have e : A'.map (cA σ) = (C5.uA_k L (-c.1))ᵀ := by
    calc A'.map (cA σ) = A'.map (cA σ) * ((C5.uA_k L c.1)ᵀ *
           (C5.uA_k L (-c.1))ᵀ) := by rw [hinv, Matrix.mul_one]
      _ = (C5.uA_k L (-c.1))ᵀ :=
            by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A' = (C5.uA_k L (-c.1))ᵀ.map (cA σ) := by
    rw [← e, Matrix.map_map]
    ext i j
    simp [cA_inv' hσ]
  rw [hA', e2]
theorem fix_cM'_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) : Fix_k L (cM c) := by
  intro k
  rw [cM_frame_k h]
  rcases k with k | k
  · simp [C5.uA_k, Matrix.one_apply, 
      Matrix.sum_apply, C4.em_ne_k L]
  · simp
theorem cM_rat'_k (h : Hyp_k L nb uM nb' w₁ cM δ) {c : (Fin L.n → AE F E) × AF F} (hu : c.1 ∈ L.ratV)
    (ha : c.2 ∈ (algebraMap F (AF F)).range) : cM c ∈ rat2 σ d.Y := by
  obtain ⟨u₀, hu₀⟩ := ComplexParameterFamilyContinuity.mem_ratVec.1 hu
  obtain ⟨a₀, ha₀⟩ := ha
  refine kunf.rat_of_inFrame (b := d.b) (M := fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u₀ j))
    (Matrix.single L.i₀ L.i₀ (a₀ • δ)) 0 ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (-u₀ j))ᵀ.map σ)) ?_
  rw [cM_frame_k h, ← hu₀, ← ha₀, Afc.incM_fromBlocks, kfour.incM_zero]
  congr 1
  · ext i k
    simp [incM, C5.uA_k, GlobalTheory.ThK.incV, single_apply,
      Matrix.one_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · ext i k
    simp only [incM, C5.aB_k, Matrix.map_apply, single_apply]
    split_ifs
    · show (algebraMap F (AF F) a₀) • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (a₀ • δ)
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        ← Algebra.algebraMap_eq_smul_one]
    · simp
  · ext i k
    have cA_inclR (x : E) : cA σ (inclR (AF F) x) = inclR (AF F) (σ x) := by
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) =
        (1 : AF F) ⊗ₜ[F] σ x
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    simp [incM, C5.uA_k, GlobalTheory.ThK.incV, single_apply,
      Matrix.one_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [cA_inclR]
theorem emS_cM_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    (inFrame d.b (cM c)).submatrix (C4.emS_k L)
      (C4.emS_k L) = 1 := by
  ext r r'
  rcases r with k | k <;> rcases r' with k' | k' <;>
    simp [cM_frame_k h, C4.emS_k,
      C5.uA_k, C5.aB_k,
      Matrix.one_apply, Matrix.sum_apply,
      L.inj.eq_iff,
      Ne.symm (C4.em_ne_k L _)]
end PositivityTheory.SiegelWeilFormula.Act.C6
end

section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C5
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {d : SD_k σ} {L : LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
namespace I
variable (L) in
theorem sum_split'_k {M : Type} [AddCommMonoid M] (f : Fin d.n → M) : ∑ i, f i = f L.i₀ + ∑ k, f (L.em k) := by
  have himg : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [L.rng i]
    rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L.i₀), ← himg, Finset.sum_image (fun a _ b _ h => L.inj h)]
theorem blk_mul_k {M N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)}
    (hM : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r (Sum.inl L.i₀))
    (hN : ∀ c, N (Sum.inr L.i₀) c = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) c) :
    (M * N).submatrix (C4.emS_k L)
      (C4.emS_k L) = M.submatrix
      (C4.emS_k L) (C4.emS_k
      L) * N.submatrix (C4.emS_k L)
      (C4.emS_k L) := by
  ext a a'
  simp only [submatrix_apply, Matrix.mul_apply]
  refine Bq.sum_emb (C4.emS_k L)
    (C4.emS_inj_k L) _ fun k hk => ?_
  rcases C4.mem_out_k L hk with rfl | rfl
  · rw [hM, Matrix.one_apply_ne, zero_mul]
    exact fun h => C4.not_inl_k L L.i₀ rfl ⟨a, h⟩
  · rw [hN, Matrix.one_apply_ne, mul_zero]
    exact fun h => C4.not_inr_k L L.i₀ rfl ⟨a', h.symm⟩
theorem blk_one_k : (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).submatrix
  (C4.emS_k L) (C4.emS_k L)
  = 1 := by
  ext a a'
  simp [Matrix.one_apply, (C4.emS_inj_k L).eq_iff]
theorem rowy_cM_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F
  E) × AF F) (k : Fin d.n ⊕ Fin d.n) :
    inFrame d.b (cM c) (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k := by
  rw [cM_frame_k h]
  rcases k with k | k
  · simp
  · by_cases hk : k = L.i₀
    · subst hk
      simp [C5.uA_k, Matrix.one_apply, single_apply,
        Matrix.sum_apply, C4.em_ne_k L]
    · simp [C5.uA_k, Matrix.one_apply, single_apply,
        Matrix.sum_apply, C4.em_ne_k L, hk, Ne.symm hk]
theorem rowy_inv_k {x : d.G}
    (hx : ∀ k, inFrame d.b x (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k) (k : Fin d.n ⊕ Fin d.n) :
    inFrame d.b x⁻¹ (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k := by
  have h1 : (inFrame d.b x * inFrame d.b x⁻¹) (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k := by
    rw [← inFrame_mul, mul_inv_cancel,
      inFrame_one]
  rw [Matrix.mul_apply, sum_eq_single (Sum.inr L.i₀)] at h1
  · rwa [hx, Matrix.one_apply_eq, one_mul] at h1
  · intro j _ hj
    rw [hx, Matrix.one_apply_ne (Ne.symm hj), zero_mul]
  · simp
theorem rowy_j_k (g : G2 σ L.Y) (k : Fin d.n ⊕ Fin d.n) :
    inFrame d.b (L.j g) (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k :=
  (L.j_out g (Sum.inr L.i₀) (by simp) k).1
theorem blk_j_k (g : G2 σ L.Y) : (inFrame d.b (L.j g)).submatrix (C4.emS_k
  L) (C4.emS_k L) = inFrame L.b g := by
  ext a a'
  rw [submatrix_apply, C4.inFrame_j_k,
    C4.padM_emS_k]
theorem weyl_embedded_columns (h : Hyp_k L nb uM nb' w₁ cM δ) (a : Fin
  L.n ⊕ Fin L.n) (l : Fin d.n ⊕ Fin d.n) :
    inFrame d.b w₁ (C4.emS_k L a) l = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin
      d.n ⊕ Fin d.n) (AE F E)) (C4.emS_k L a) l ∧
      inFrame d.b w₁ l (C4.emS_k L a) = (1 : Matrix (Fin d.n ⊕ Fin d.n)
        (Fin d.n ⊕ Fin d.n) (AE F E)) l (C4.emS_k L a) := by
  obtain ⟨a₀, b₀, -, -, hW⟩ := h.wf
  rw [hW]
  have hne := C4.em_ne_k L
  rcases a with a | a <;>
    simp [C4.emS_k, single_apply, Matrix.one_apply, hne a,
      Ne.symm (hne a)] <;>
    (constructor <;> congr)
theorem weyl_base_rows (h : Hyp_k L nb uM nb' w₁ cM δ) : ∃ b₀ : E,
  b₀ ≠ 0 ∧
    (∀ l, inFrame d.b w₁ (Sum.inr L.i₀) l = if l = Sum.inl L.i₀ then inclR (AF F) b₀ else 0) ∧
    ∀ j l, inFrame d.b w₁ (Sum.inr (L.em j)) l =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (L.em j)) l := by
  obtain ⟨a₀, b₀, -, hb, hW⟩ := h.wf
  refine ⟨b₀, hb, fun l => ?_, fun j l => (weyl_embedded_columns h (Sum.inr j) l).1⟩
  rw [hW]
  rcases l with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [single_apply, Matrix.one_apply]
  · simp [single_apply, Matrix.one_apply, hi, Ne.symm hi]
  · subst hi; simp [single_apply, Matrix.one_apply]
  · simp [single_apply, Matrix.one_apply, hi, Ne.symm hi]
theorem row_eq_k {P Wm C C' : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)} {b : AE F E}
    (hP : ∀ i, P (Sum.inr L.i₀) (Sum.inl i) = 0)
    (hWy : ∀ l, Wm (Sum.inr L.i₀) l = if l = Sum.inl L.i₀ then b else 0)
    (hWo : ∀ j l, Wm (Sum.inr (L.em j)) l =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (L.em j)) l)
    (hE : P * (Wm * C) = Wm * C') (k : Fin d.n ⊕ Fin d.n) :
    b * C' (Sum.inl L.i₀) k = P (Sum.inr L.i₀) (Sum.inr L.i₀) * (b * C (Sum.inl L.i₀) k) +
      ∑ j, P (Sum.inr L.i₀) (Sum.inr (L.em j)) * C (Sum.inr (L.em j)) k := by
  have hy : ∀ X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E),
      (Wm * X) (Sum.inr L.i₀) k = b * X (Sum.inl L.i₀) k := by
    intro X
    rw [Matrix.mul_apply, sum_eq_single (Sum.inl L.i₀)]
    · rw [hWy, ite_eq_left rfl]
    · intro l _ hl
      rw [hWy, ite_eq_right hl, zero_mul]
    · simp
  have hem : ∀ j, (Wm * C) (Sum.inr (L.em j)) k = C (Sum.inr (L.em j)) k := by
    intro j
    rw [Matrix.mul_apply, sum_eq_single (Sum.inr (L.em j))]
    · rw [hWo, Matrix.one_apply_eq, one_mul]
    · intro l _ hl
      rw [hWo, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
    · simp
  have e := congrFun (congrFun hE (Sum.inr L.i₀)) k
  rw [← hy C', ← e, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hP, zero_mul, Finset.sum_const_zero, zero_add]
  rw [sum_split'_k L (fun i => P (Sum.inr L.i₀) (Sum.inr i) * (Wm * C) (Sum.inr i) k), hy C]
  simp only [hem]
theorem cx_em_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E)
  × AF F) (m : Fin L.n) :
    inFrame d.b (cM c) (Sum.inl L.i₀) (Sum.inl (L.em m)) = c.1 m := by
  rw [cM_frame_k h]
  simp [C5.uA_k, Matrix.one_apply, single_apply, Matrix.sum_apply,
    C4.em_ne_k L, L.inj.eq_iff,
    Ne.symm (C4.em_ne_k L _)]
theorem cx_emr_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F
  E) × AF F) (m : Fin L.n) :
    inFrame d.b (cM c) (Sum.inl L.i₀) (Sum.inr (L.em m)) = 0 := by
  rw [cM_frame_k h]
  simp [C5.aB_k, single_apply,
    C4.em_ne_k L,
    Ne.symm (C4.em_ne_k L _)]
theorem cx_y_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E)
  × AF F) :
    inFrame d.b (cM c) (Sum.inl L.i₀) (Sum.inr L.i₀) = c.2 • inclR (AF F) δ := by
  rw [cM_frame_k h]
  simp [C5.aB_k]
theorem cem_l_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E)
  × AF F) (j : Fin L.n) (l : Fin d.n) :
    inFrame d.b (cM c) (Sum.inr (L.em j)) (Sum.inl l) = 0 := by
  rw [cM_frame_k h]
  simp
theorem cem_em_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F
  E) × AF F) (j m : Fin L.n) :
    inFrame d.b (cM c) (Sum.inr (L.em j)) (Sum.inr (L.em m)) =
      (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) j m := by
  rw [cM_frame_k h]
  by_cases hjm : j = m
  · subst hjm
    simp [C5.uA_k, Matrix.one_apply, single_apply,
      Matrix.sum_apply, C4.em_ne_k L,
      Ne.symm (C4.em_ne_k L _)]
  · simp [C5.uA_k, Matrix.one_apply, single_apply,
      Matrix.sum_apply, C4.em_ne_k L,
      Ne.symm (C4.em_ne_k L _),
      L.inj.eq_iff, hjm, Ne.symm hjm]
theorem inj_core_k (h : Hyp_k L nb uM nb' w₁ cM δ) {p : d.G} (hp : p ∈
  par2 σ d.Y) (_hpr : p ∈ rat2 σ d.Y) {c c' : Cr_k L}
    {γ' γ'' : G2 σ L.Y} (h' : γ' ∈ rat2 σ L.Y) (_h'' : γ'' ∈ rat2 σ L.Y)
    (e : p * (w₁ * (cM c.1 * L.j γ')) = w₁ * (cM c'.1 * L.j γ'')) :
    γ'' * γ'⁻¹ ∈ par2 σ L.Y ∧ (γ'' = γ' → c = c') := by
  have hP21 : (inFrame d.b p).toBlocks₂₁ = 0 := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block
    d.ok.frame p).1 hp
  have hP : ∀ i k, inFrame d.b p (Sum.inr i) (Sum.inl k) = 0 := fun i k => congrFun (congrFun hP21 i) k
  refine ⟨?_, fun hγ => ?_⟩
  ·
    set g := γ'' * γ'⁻¹ with hg
    have key : w₁⁻¹ * p * w₁ * (cM c.1 * L.j γ') = cM c'.1 * L.j γ'' := by
      rw [mul_assoc (w₁⁻¹ * p), mul_assoc w₁⁻¹, e, inv_mul_cancel_left]
    have key2 : w₁⁻¹ * p * w₁ = cM c'.1 * L.j g * (cM c.1)⁻¹ := by
      rw [hg, map_mul, map_inv, ← mul_assoc (cM c'.1), ← key]
      group
    have hQ : (inFrame d.b (w₁⁻¹ * p * w₁)).submatrix (C4.emS_k L)
      (C4.emS_k L) = (inFrame d.b p).submatrix
      (C4.emS_k L) (C4.emS_k
      L) := by
      have hWQ : inFrame d.b w₁ * inFrame d.b (w₁⁻¹ * p * w₁) = inFrame d.b p * inFrame d.b w₁ := by
        rw [← inFrame_mul, ← inFrame_mul,
          ← mul_assoc, ← mul_assoc, mul_inv_cancel,
          one_mul]
      ext a a'
      have e1 := congrFun (congrFun hWQ (C4.emS_k L a))
        (C4.emS_k L a')
      rw [Matrix.mul_apply, Matrix.mul_apply,
        Finset.sum_eq_single (C4.emS_k L a),
        Finset.sum_eq_single (C4.emS_k L a')] at e1
      · rw [(weyl_embedded_columns h a (C4.emS_k L a)).1,
          (weyl_embedded_columns h a' (C4.emS_k L a')).2,
          Matrix.one_apply_eq, Matrix.one_apply_eq, one_mul, mul_one] at e1
        exact e1
      · intro l _ hl
        rw [(weyl_embedded_columns h a' l).2, Matrix.one_apply_ne hl, mul_zero]
      · simp
      · intro l _ hl
        rw [(weyl_embedded_columns h a l).1, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
      · simp
    have hfixC' := fix_cM'_k h c'.1
    have hC1 : (inFrame d.b (cM c.1)⁻¹).submatrix (C4.emS_k L)
      (C4.emS_k L) = 1 := by
      have h1 := blk_mul_k (L := L) (M := inFrame d.b (cM c.1)) (N := inFrame d.b (cM c.1)⁻¹)
        (fix_cM'_k h c.1)
        (rowy_inv_k (rowy_cM_k h c.1))
      rw [← inFrame_mul, mul_inv_cancel,
        inFrame_one, blk_one_k,
        emS_cM_k h, one_mul] at h1
      exact h1.symm
    have hR : (inFrame d.b (cM c'.1 * L.j g * (cM c.1)⁻¹)).submatrix
      (C4.emS_k L) (C4.emS_k
      L) = inFrame L.b g := by
      rw [inFrame_mul,
        blk_mul_k (fix_mul_k hfixC'
        (fix_j_k g)) (rowy_inv_k (rowy_cM_k h c.1)),
        inFrame_mul, blk_mul_k hfixC' (rowy_j_k g),
          emS_cM_k h, blk_j_k, hC1, one_mul, mul_one]
    have hG : inFrame L.b g = (inFrame d.b p).submatrix (C4.emS_k L)
      (C4.emS_k L) := by
      rw [← hR, ← key2, hQ]
    refine (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.ok.frame g).2 ?_
    ext i k
    rw [hG]
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, submatrix_apply, Matrix.zero_apply,
      C4.emS_k, Sum.map_inr,
      Sum.map_inl]
    exact hP _ _
  ·
    subst hγ
    have e2 : p * w₁ * cM c.1 = w₁ * cM c'.1 := by
      have h1 := congrArg (· * (L.j γ'')⁻¹) e
      simpa [mul_assoc] using h1
    have hE : inFrame d.b p * (inFrame d.b w₁ * inFrame d.b (cM c.1)) = inFrame d.b w₁ * inFrame d.b (cM c'.1) := by
      have h1 := congrArg (inFrame d.b) e2
      simpa only [inFrame_mul, Matrix.mul_assoc] using h1
    obtain ⟨b₀, hb₀, hWy, hWo⟩ := weyl_base_rows h
    have hrow := row_eq_k (fun i => hP L.i₀ i) hWy hWo hE
    set bA := inclR (F := F) (E := E) (AF F) b₀
    have hbinv : inclR (F := F) (E := E) (AF F) b₀⁻¹ * bA = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb₀, map_one]
    have canc : ∀ X Y : AE F E, bA * X = bA * Y → X = Y := by
      intro X Y hXY
      have h1 := congrArg (inclR (F := F) (E := E) (AF F) b₀⁻¹ * ·) hXY
      simpa only [← mul_assoc, hbinv, one_mul] using h1
    have hfixC := fix_cM'_k h c.1
    have hfixC' := fix_cM'_k h c'.1
    have hyy : inFrame d.b p (Sum.inr L.i₀) (Sum.inr L.i₀) = 1 := by
      have h1 := hrow (Sum.inl L.i₀)
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inl L.i₀) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hfixC, Matrix.one_apply_ne (by simp), mul_zero]
      rw [hs, add_zero, hfixC', hfixC, Matrix.one_apply_eq, mul_one] at h1
      exact canc _ _ (by rw [mul_one, mul_comm]; exact h1.symm)
    have hd : ∀ l, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em l)) = 0 := by
      intro l
      have h1 := hrow (Sum.inr (L.em l))
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inr (L.em l)) = inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em l))
            := by
        rw [Finset.sum_eq_single l]
        · rw [cem_em_k h, Matrix.one_apply_eq, mul_one]
        · intro j _ hj
          rw [cem_em_k h, Matrix.one_apply_ne hj, mul_zero]
        · simp
      rw [hs, cx_emr_k h, cx_emr_k h] at h1
      simp only [mul_zero, zero_add] at h1
      exact h1.symm
    have hu : ∀ m, c'.1.1 m = c.1.1 m := by
      intro m
      have h1 := hrow (Sum.inl (L.em m))
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inl (L.em m)) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [cem_l_k h, mul_zero]
      rw [hs, add_zero, cx_em_k h, cx_em_k h, hyy, one_mul] at h1
      exact canc _ _ h1
    have ha : c'.1.2 = c.1.2 := by
      have h1 := hrow (Sum.inr L.i₀)
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inr L.i₀) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hd, zero_mul]
      rw [hs, add_zero, cx_y_k h, cx_y_k h, hyy, one_mul] at h1
      exact smul_inclR_inj h.δ0 (canc _ _ h1)
    exact Subtype.ext (Prod.ext (funext fun m => (hu m).symm) ha.symm)
end I
end PositivityTheory.SiegelWeilFormula.Act.C6
end

section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
  PositivityTheory.SiegelWeilFormula.Act.C5
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {d : SD_k σ} {L : LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
namespace N
theorem fix_of_col_k {w x : d.G}
    (hc : ∀ r,
      inFrame d.b x r (Sum.inl L.i₀) = inFrame d.b w r (Sum.inl L.i₀)) :
      Fix_k L (w⁻¹ * x) := by
  intro k
  rw [inFrame_mul, Matrix.mul_apply]
  simp_rw [hc]
  rw [← Matrix.mul_apply, ← inFrame_mul, inv_mul_cancel,
    inFrame_one]
theorem weyl_base_column (h : Hyp_k L nb uM nb' w₁ cM δ) : ∃ b₀ : E,
  b₀ ≠ 0 ∧ ∀ r, inFrame d.b w₁ r (Sum.inl L.i₀) =
    inclR (AF F) ((Pi.single (Sum.inr L.i₀) b₀ : Fin d.n ⊕ Fin d.n → E) r) := by
  obtain ⟨a, b, -, hb, hw⟩ := h.wf
  refine ⟨b, hb, fun r => ?_⟩
  rw [hw]
  rcases r with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
  · subst hi; simp [single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
theorem normalize_k (h : Hyp_k L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈
  rat2 σ d.Y) (hn : ¬ FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ Fix_k L (w₁⁻¹ * (p * γ)) := by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  have hform := Bq.form_E hε γ hG0
  obtain ⟨b₀, hb₀, hw1⟩ := weyl_base_column h
  have hy : (fun k => G0 (Sum.inr k) (Sum.inl L.i₀)) ≠ 0 := by
    intro h0
    apply hn
    intro i
    rw [hG0]
    show inclR (F := F) (AF F) (G0 (Sum.inr i) (Sum.inl L.i₀)) = 0
    rw [congrFun h0 i, Pi.zero_apply, map_zero]
  obtain ⟨A, β0, hβ, hcol⟩ := exists_E L.i₀ hσ ε hform hb₀ hy
  obtain ⟨pm, hpmr, hpm⟩ := Afc.levi_ex hσ d.ok.frame A
  have hpmP : pm ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pm).2
      (by rw [hpm, toBlocks_fromBlocks₂₁])
  have hβA : incM F β0 ∈ nA σ d.Y d.b := (kfour.mem_nA_iff hσ hε _).2 (nCond_of_E ε hβ)
  set pn := nb ⟨incM F β0, hβA⟩ with hpn_def
  have hpn : inFrame d.b pn = fromBlocks 1 (incM F β0) 0 1 := h.nb _
  have hpnP : pn ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pn).2
      (by rw [hpn, toBlocks_fromBlocks₂₁])
  have hpnr : pn ∈ rat2 σ d.Y :=
    kunf.rat_of_inFrame (M := fromBlocks 1 β0 0 1) (by rw [hpn, kfour.incM_nM]; rfl)
  refine ⟨pn * pm, mul_mem hpnP hpmP, mul_mem hpnr hpmr, fix_of_col_k fun r => ?_⟩
  have hF : inFrame d.b (pn * pm * γ) =
      incM F (fromBlocks 1 β0 0 1 * fromBlocks A.1 0 0 (((A⁻¹).1)ᵀ.map σ) * G0) := by
    rw [inFrame_mul, inFrame_mul, hpn, hpm, hG0,
      kfour.incM_mul', kfour.incM_mul',
      kfour.incM_nM, Afc.incM_fromBlocks, kfour.incM_zero]
    rfl
  rw [hF, hw1 r]
  show inclR (F := F) (AF F) _ = _
  rw [hcol r]
end N
variable (L) in
def sExp_k (e : AE F E) (b : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  fromBlocks 1 (∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(e * cA σ (b j))))) 0 1
theorem nq_cM_k (h : Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (cM c)) := by
  rw [cM_frame_k h]
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rcases k with k | k <;>
      simp [Matrix.one_apply, C5.uA_k, 
        Matrix.sum_apply, C4.em_ne_k L]
  · rcases k with k | k <;> rcases l with l | l
    · have hk : k ≠ L.i₀ := fun e => hkx (by rw [e])
      simp [Matrix.one_apply, C5.uA_k, 
        Matrix.sum_apply, Ne.symm hk]
    · have hk : k ≠ L.i₀ := fun e => hkx (by rw [e])
      simp [C5.aB_k, Ne.symm hk]
    · simp
    · have hl : l ≠ L.i₀ := fun e => hly (by rw [e])
      simp [Matrix.one_apply, C5.uA_k, 
        Matrix.sum_apply, Ne.symm hl]
namespace B
variable (L) in
def sb_k (e : AE F E) (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(e * cA σ (b j))))
theorem sExp_eq_k (e : AE F E) (b : Fin L.n → AE F E) : sExp_k L e b =
  fromBlocks 1 (sb_k L e b) 0 1 := rfl
theorem hne_k (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩
theorem section_base_base_entry (e : AE F E) (b : Fin L.n → AE F E) : sb_k L e b L.i₀ L.i₀ = 0 := by
  simp [sb_k, Matrix.sum_apply, hne_k]
theorem section_base_row_entry (e : AE F E) (b : Fin L.n → AE F E) (k : Fin L.n) : sb_k L e b L.i₀ (L.em k) = b k := by
  simp [sb_k, Matrix.sum_apply, single_apply, hne_k, L.inj.eq_iff]
theorem section_entry_row_base (e : AE F E) (b : Fin L.n → AE F E) (k : Fin L.n) :
    sb_k L e b (L.em k) L.i₀ = -(e * cA σ (b k)) := by
  simp [sb_k, Matrix.sum_apply, single_apply, hne_k, L.inj.eq_iff]
theorem sb_em_em_k (e : AE F E) (b : Fin L.n → AE F E) (j k : Fin L.n) : sb_k L e b (L.em j) (L.em k) = 0 := by
  simp [sb_k, Matrix.sum_apply, (hne_k j).symm, (hne_k k).symm]
theorem unipotent_base_base_entry (u : Fin L.n → AE F E) : C5.uA_k L u
  L.i₀ L.i₀ = 1 := by
  simp [C5.uA_k, Matrix.sum_apply, hne_k]
theorem unipotent_base_row_entry (u : Fin L.n → AE F E) (k : Fin L.n) :
  C5.uA_k L u L.i₀ (L.em k) = u k := by
  simp [C5.uA_k, Matrix.sum_apply, single_apply, 
    L.inj.eq_iff, Ne.symm (hne_k k)]
theorem uA_em_em_k (u : Fin L.n → AE F E) (j k : Fin L.n) : C5.uA_k L u
  (L.em j) (L.em k) = if j = k then 1 else 0 := by
  simp [C5.uA_k, Matrix.sum_apply, Matrix.one_apply,
    L.inj.eq_iff, (hne_k j).symm]
theorem centre_base_base_entry (a : AF F) : C5.aB_k L δ a L.i₀ L.i₀ = a •
  inclR (AF F) δ := by
  simp [C5.aB_k]
theorem centre_base_row_entry (a : AF F) (k : Fin L.n) : C5.aB_k L δ a
  L.i₀ (L.em k) = 0 := by
  simp [C5.aB_k, Ne.symm (hne_k k)]
end B
open B in
theorem nq_sExp_k (e : AE F E) (b : Fin L.n → AE F E) : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (sExp_k L e b) := by
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rcases k with a | a <;> simp [B.sExp_eq_k, Matrix.one_apply]
  · rcases k with a | a <;> rcases l with c | c
    · simp [B.sExp_eq_k, Matrix.one_apply]
    · have ha : a ≠ L.i₀ := fun h => hkx (by rw [h])
      have hc : c ≠ L.i₀ := fun h => hly (by rw [h])
      obtain ⟨j, rfl⟩ := (L.rng a).1 ha
      obtain ⟨k, rfl⟩ := (L.rng c).1 hc
      simp [B.sExp_eq_k, B.sb_em_em_k]
    · simp [B.sExp_eq_k]
    · simp [B.sExp_eq_k, Matrix.one_apply]
open B in
theorem U_sExp_k {ε : ℤˣ} (hσ : ∀ a, σ (σ a) = a) (b : Fin L.n → AE F E) :
    M.U (cA σ).toRingHom (((ε : ℤ) : AE F E)) (sExp_k L (((ε : ℤ) : AE F E)) b) := by
  set e := ((ε : ℤ) : AE F E) with he
  have hee : e * e = 1 := by rw [he, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hce : cA σ e = e := by rw [he, map_intCast]
  have hcc := cA_inv' hσ
  unfold M.U
  show (sExp_k L e b)ᵀ * kunf.jw d.n e * (sExp_k L e b).map (cA σ) = kunf.jw d.n e
  rw [B.sExp_eq_k, kunf.nmat_form]
  have h0 : e • (B.sb_k L e b).map (cA σ) + (B.sb_k L e b)ᵀ = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, transpose_apply, Matrix.zero_apply,
      smul_eq_mul]
    by_cases hp : p = L.i₀
    · subst hp
      by_cases hq : q = L.i₀
      · subst hq; simp [B.section_base_base_entry]
      · obtain ⟨k, rfl⟩ := (L.rng q).1 hq
        rw [B.section_base_row_entry, B.section_entry_row_base]; ring
    · obtain ⟨j, rfl⟩ := (L.rng p).1 hp
      by_cases hq : q = L.i₀
      · subst hq
        rw [B.section_entry_row_base, B.section_base_row_entry, map_neg, map_mul, hce, hcc]
        linear_combination (-(b j)) * hee
      · obtain ⟨k, rfl⟩ := (L.rng q).1 hq
        simp [B.sb_em_em_k]
  rw [h0]
  rfl
theorem delta_par_k (h : Hyp_k L nb uM nb' w₁ cM δ) {ε : ℤˣ} (hε : kfour.FrameEq σ d.Y d.b ε) :
    σ δ = -(((ε : ℤ) : E) * δ) := by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have hU : M.U (cA σ).toRingHom (((ε : ℤ) : AE F E)) (inFrame d.b (cM (0, 1))) := kunf.frame_eq hε (cM (0, 1))
  have he : (((ε : ℤ) : AE F E)) * (((ε : ℤ) : AE F E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : (cA σ).toRingHom (((ε : ℤ) : AE F E)) = ((ε : ℤ) : AE F E) := map_intCast _ _
  have hp := M.even_im_hermitian_sub (fun z => cA_inv' hσ z) he hse L.em L.inj L.rng hU (nq_cM_k h (0, 1))
  rw [cM_frame_k h] at hp
  simp [C5.aB_k, C5.uA_k,
    C4.em_ne_k L,
    Ne.symm ( _)] at hp
  have hc (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := rfl
  apply kfour.inclR_injective (F := F)
  rw [hc] at hp
  simpa only [map_neg, map_mul, map_intCast] using hp
open B in
theorem row_sC_k (h : Hyp_k L nb uM nb' w₁ cM δ) (e : AE F E) (b u : Fin L.n → AE F E) (a : AF F) :
    (∀ j, (sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inl (L.em j)) = u j) ∧
    (∀ j, (sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inr (L.em j)) = b j) ∧
    (sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inr L.i₀) =
      a • inclR (AF F) δ - ∑ j, b j * cA σ (u j) ∧
    (sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inl L.i₀) = 1 := by
  rw [cM_frame_k h, B.sExp_eq_k, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, 
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
  have hs : ∀ q,
    (B.sb_k L e b * (C5.uA_k L (-u))ᵀ.map (cA σ)) L.i₀ q = ∑ k,
    b k * cA σ (C5.uA_k L (-u) q (L.em k)) := by
    intro q
    rw [Matrix.mul_apply, M.sum_split' L.em L.inj L.rng, B.section_base_base_entry, zero_mul, zero_add]
    simp only [B.section_base_row_entry, Matrix.map_apply, transpose_apply]
  refine ⟨fun j => B.unipotent_base_row_entry u j, fun j => ?_, ?_, B.unipotent_base_base_entry u⟩
  · rw [Matrix.add_apply, B.centre_base_row_entry, zero_add, hs]
    simp [B.uA_em_em_k, apply_ite (cA σ)]
  · rw [Matrix.add_apply, B.centre_base_base_entry, hs, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [B.unipotent_base_row_entry, Pi.neg_apply, map_neg, mul_neg]
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end
