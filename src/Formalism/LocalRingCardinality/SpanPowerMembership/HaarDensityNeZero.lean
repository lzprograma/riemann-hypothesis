module

public import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsDensity
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsOmegaLeb
public import Mathlib.Analysis.Matrix.Normed
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Filter Topology Metric NormedSpace Set Matrix Formalism.UG.P
open scoped ENNReal NNReal Matrix.Norms.Operator

variable (P Q : ℕ)

local notation "J" => Formalism.UG.Jpq P Q

def matHom : UpqT P Q →* MM P Q where
  toFun := UpqT.mat
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mat_mem (g : UpqT P Q) : (UpqT.mat g)ᴴ * J * UpqT.mat g = J := g.2

theorem mat_inducing : IsInducing (UpqT.mat : UpqT P Q → MM P Q) := by
  exact Units.isOpenEmbedding_val.toIsEmbedding.toIsInducing.comp Topology.IsInducing.subtypeVal

theorem mat_injective : Function.Injective (UpqT.mat : UpqT P Q → MM P Q) := fun _ _ h => Subtype.ext (Units.ext h)

theorem mat_embedding : IsEmbedding (UpqT.mat : UpqT P Q → MM P Q) := ⟨mat_inducing P Q, mat_injective P Q⟩

theorem exists_of_mem (h : MM P Q) (hh : hᴴ * J * h = J) : ∃ g : UpqT P Q, UpqT.mat g = h := by
  have hl : J * hᴴ * J * h = 1 := by
    calc J * hᴴ * J * h = J * (hᴴ * J * h) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, J_sq]
  have hr : h * (J * hᴴ * J) = 1 := mul_eq_one_comm.mp hl
  exact ⟨⟨⟨h, J * hᴴ * J, hr, hl⟩, hh⟩, rfl⟩

theorem mat_range : Set.range (UpqT.mat : UpqT P Q → MM P Q) = {h | hᴴ * J * h = J} := by
  ext h
  exact ⟨fun ⟨g, hg⟩ => hg ▸ mat_mem P Q g, exists_of_mem P Q h⟩

theorem mat_closedEmbedding : IsClosedEmbedding (UpqT.mat : UpqT P Q → MM P Q) := by
  refine ⟨mat_embedding P Q, ?_⟩
  rw [mat_range]
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

instance : LocallyCompactSpace (UpqT P Q) :=
  haveI : LocallyCompactSpace (MM P Q) :=
    inferInstanceAs (LocallyCompactSpace (Fin P ⊕ Fin Q → Fin P ⊕ Fin Q → ℂ))
  (mat_closedEmbedding P Q).locallyCompactSpace

instance (N : ℕ) : CompactSpace (UpqT N 0) :=
  isCompact_iff_compactSpace.mp (indefinite_unitary_compact N)

theorem exp_neg_mul' (X : MM P Q) : exp (-X) * exp X = 1 := by
  have h := NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl X))
  rw [neg_add_cancel, NormedSpace.exp_zero] at h
  exact h.symm

theorem exp_conjJ (A : MM P Q) : exp (J * A * J) = J * exp A * J := by
  exact NormedSpace.exp_units_conj ⟨J, J, J_sq P Q, J_sq P Q⟩ A

theorem exp_mem (X : MM P Q) (hX : X ∈ lieU P Q) : (exp X)ᴴ * J * exp X = J := by
  have h1 : J * (-Xᴴ) * J = X := (mem_lieU_iff P Q X).1 hX
  have e : J * (J * (-Xᴴ) * J) * J = -Xᴴ := by
    rw [mul_assoc, mul_assoc (J * (-Xᴴ)), J_sq, mul_one, ← mul_assoc, J_sq, one_mul]
  have h2 : Xᴴ = J * (-X) * J := by
    rw [h1] at e
    rw [mul_neg, neg_mul, e, neg_neg]
  rw [← Matrix.exp_conjTranspose, h2, exp_conjJ]
  simp [Matrix.mul_assoc, J_sq, exp_neg_mul']

theorem exp_theta (Z : MM P Q) (hZ : (exp Z)ᴴ * J * exp Z = J) : exp (J * (-Zᴴ) * J) = exp Z := by
  rw [← Matrix.exp_conjTranspose Z] at hZ
  have h1 : J * exp Z = exp (-Zᴴ) * J := by
    calc J * exp Z = exp (-Zᴴ) * exp Zᴴ * J * exp Z := by rw [exp_neg_mul', one_mul]
      _ = exp (-Zᴴ) * (exp Zᴴ * J * exp Z) := by simp only [mul_assoc]
      _ = exp (-Zᴴ) * J := by rw [hZ]
  rw [exp_conjJ]
  calc J * exp (-Zᴴ) * J = J * (J * exp Z) := by rw [mul_assoc, ← h1]
    _ = exp Z := by rw [← mul_assoc, J_sq, one_mul]

def chart : Chart (lieU P Q) (UpqT P Q) where
  mat := matHom P Q
  emb := mat_embedding P Q
  H1 := fun X => exists_of_mem P Q _ (exp_mem P Q X X.2)
  H2 := by
    have hθ : Continuous (fun Z : MM P Q => J * (-Zᴴ) * J) :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose.neg).matrix_mul continuous_const
    have h0 : Tendsto (fun Z : MM P Q => J * (-Zᴴ) * J) (𝓝 0) (𝓝 0) := by
      have := hθ.tendsto 0
      simpa using this
    filter_upwards [logA_exp (𝔸 := MM P Q), h0.eventually (logA_exp (𝔸 := MM P Q))] with Z h1 h2
    rintro ⟨g, hg⟩
    have hm : (exp Z)ᴴ * J * exp Z = J := by
      have := mat_mem P Q g
      rw [show UpqT.mat g = exp Z from hg] at this
      exact this
    rw [mem_lieU_iff]
    calc J * (-Zᴴ) * J = logA (𝔸 := MM P Q) (exp (J * (-Zᴴ) * J)) := h2.symm
      _ = logA (𝔸 := MM P Q) (exp Z) := congrArg (logA (𝔸 := MM P Q)) (exp_theta P Q Z hm)
      _ = Z := h1

theorem norm_le_sum (X : MM P Q) : ‖X‖ ≤ ∑ i, ∑ j, ‖X i j‖ := by
  rw [Matrix.linfty_opNorm_def (A := X)]
  simpa [NNReal.coe_sum] using
    NNReal.coe_le_coe.mpr (Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊) (fun _ _ => zero_le)
        (Finset.mem_univ i))

theorem omegaDensity_haar (μ : Measure (UpqT P Q)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ OmegaDensity μ c := by
  obtain ⟨lam, hlam⟩ := exists_omegaLeb P Q
  have := hlam.1
  obtain ⟨c, hc0, hct, h⟩ := (chart P Q).exists_density' (finDimLie P Q) _ (instBorelLie P Q) _
    (instBorelU P Q) (instTopGroupU P Q) μ inferInstance lam hlam.1
  refine ⟨c, hc0, hct, lam, hlam, ?_⟩
  exact h (ballU P Q) (fun r => (isOpen_ballU P Q r).measurableSet)
    (fun δ hδ => by
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr X hX
      exact lt_of_le_of_lt (norm_le_sum P Q X) (lt_trans hX hr.2))
    (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact ⟨(ballU_pos P Q lam hr).ne', (ballU_lt_top P Q lam r).ne⟩)

theorem omegaDensity_smul {μ : Measure (UpqT P Q)} {c : ℝ≥0∞} (h : OmegaDensity μ c) (t : ℝ≥0∞)
    (ht : t ≠ ⊤) : OmegaDensity (t • μ) (t * c) := by
  obtain ⟨lam, hl, hc⟩ := h
  refine ⟨lam, hl, ?_⟩
  simpa [Measure.smul_apply, smul_eq_mul, mul_div_assoc] using ENNReal.Tendsto.const_mul hc (Or.inr ht)

def mu0 : Measure (UpqT P Q) := Measure.haar

instance : (mu0 P Q).IsHaarMeasure := inferInstanceAs (Measure.haar.IsHaarMeasure)

def c0 : ℝ≥0∞ := (omegaDensity_haar P Q (mu0 P Q)).choose

def mass (N : ℕ) : ℝ≥0∞ := mu0 N 0 Set.univ

def scale : ℝ≥0∞ := c0 (P + Q) 0 / (mass (P + Q) * c0 P Q)

end Formalism.BasicNotions.Examples₂.CD
