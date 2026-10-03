import Mathlib

open Set Filter Metric
open scoped Topology ContDiff

/-- A map is completely continuous if it is continuous and maps bounded sets to
relatively compact sets. -/
def CompletelyContinuous
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E → F) : Prop :=
  Continuous T ∧
  ∀ A : Set E, Bornology.IsBounded A → IsCompact (closure (T '' A))

/-- Complete continuity on the admissible domain, rather than on negative
functions outside the paper's hypotheses. -/
def CompletelyContinuousOn
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E → F) (D : Set E) : Prop :=
  ContinuousOn T D ∧
  ∀ A : Set E, A ⊆ D → Bornology.IsBounded A → IsCompact (closure (T '' A))

/-!
# Nonlocal elliptic equations (Stańczy, 2001)

A Lean formalization/specification of the main constructions and statements in
R. Stańczy, *Nonlocal elliptic equations*, Nonlinear Analysis 47 (2001), 3579–3584.

This revision proves all coneP1D_* results and replaces 23 of the 24
custom axioms from the original specification with explicit proofs.
The sole remaining custom axiom is the Krasnoselskii cone compression/expansion
principle, named guo_lakshmikantham_fixed_point. All analytical assertions,
operator compactness results, BVP equivalences and existence results are proved.
The existence results use that fixed-point principle; the BVP equivalences,
compactness results and cone properties use only Lean/Mathlib logical axioms.
Necessary corrections to the original specification are retained:
closedness and nontriviality of the cone, extended-real limsup, and the positive
radial kernel sign. The annulus threshold uses the weight integral to power β.
The file follows the paper's numbering:
* (2)–(5): one-dimensional boundary value problem, Green function, cone and operator;
* Theorem 2.1: Guo–Lakshmikantham cone compression/expansion theorem;
* Theorem 2.2: existence in the one-dimensional case;
* Examples 1–3 and Remark 1;
* (11)–(15): radial annulus problem, Green function, operator and cone;
* Theorem 3.1 and Remarks 2–3.

Important formalization note:
Standalone source: only Mathlib is required; no Jmaa module is imported.
Validation target: Lean 4.35.0-rc3, Mathlib commit
8e30cac82f69c18f6cbe88799bdc3ebd74cc592d.
In a Mathlib-enabled project run: lake env lean Stanczy2001.lean
The six formerly axiomatized analytical results have been checked with
#print axioms: only existence_1D and existence_annulus depend on the explicitly
retained cone fixed-point axiom. No sorry, admit or additional custom axiom is used.
A checked counterexample to the old, unrestricted fixed-point statement
is included as originalRealConeFixedPointPrinciple_false.
-/

namespace Stanczy2001

/-! ## 1. Abstract fixed point theorem in a cone -/

/-- A (pointed) cone in a real normed space. -/
structure Cone (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  isClosed : IsClosed carrier
  add_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier
  smul_mem : ∀ {c : ℝ} {x}, 0 ≤ c → x ∈ carrier → c • x ∈ carrier
  strict : ∀ {x}, x ∈ carrier → -x ∈ carrier → x = 0

/-- Theorem 2.1 (Guo and Lakshmikantham, cited in Stańczy 2001).

This is the cone compression/expansion fixed-point theorem used in the paper.
UNPROVED in this file. The previous statement was false for the cone {0}.
The added nontriviality assumption corrects that defect; the theorem itself
still requires a formal proof of the cone compression/expansion principle.
-/
axiom guo_lakshmikantham_fixed_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Cone E)
    (hP_nontrivial : ∃ x ∈ P.carrier, x ≠ 0)
    (Ω₁ Ω₂ : Set E)
    (h_open₁ : IsOpen Ω₁) (h_open₂ : IsOpen Ω₂)
    (h_zero : (0 : E) ∈ Ω₁)
    (h_sub : closure Ω₁ ⊆ Ω₂)
    (h_bounded₁ : Bornology.IsBounded Ω₁)
    (h_bounded₂ : Bornology.IsBounded Ω₂)
    (S : E → E)
    (hS_cone : MapsTo S (P.carrier ∩ (closure Ω₂ \ Ω₁)) P.carrier)
    (hS_compact : IsCompact (closure (S '' (P.carrier ∩ (closure Ω₂ \ Ω₁)))))
    (hS_cont : ContinuousOn S (P.carrier ∩ (closure Ω₂ \ Ω₁)))
    (h_cond :
      ((∀ x ∈ P.carrier ∩ frontier Ω₁, ‖S x‖ ≤ ‖x‖) ∧
       (∀ x ∈ P.carrier ∩ frontier Ω₂, ‖x‖ ≤ ‖S x‖)) ∨
      ((∀ x ∈ P.carrier ∩ frontier Ω₁, ‖x‖ ≤ ‖S x‖) ∧
       (∀ x ∈ P.carrier ∩ frontier Ω₂, ‖S x‖ ≤ ‖x‖))) :
    ∃ x ∈ P.carrier ∩ (closure Ω₂ \ Ω₁), S x = x

/-- The sole fixed-point axiom specialized to two concentric balls. -/
lemma cone_fixedPoint_between_spheres
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Cone E) (hP : ∃ x ∈ P.carrier, x ≠ 0) (T : E → E)
    (hT : MapsTo T P.carrier P.carrier)
    (hCC : CompletelyContinuousOn T P.carrier)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hexpand : ∀ x ∈ P.carrier, ‖x‖ = r → ‖x‖ ≤ ‖T x‖)
    (hcompress : ∀ x ∈ P.carrier, ‖x‖ = R → ‖T x‖ ≤ ‖x‖) :
    ∃ x ∈ P.carrier, T x = x ∧ r ≤ ‖x‖ ∧ ‖x‖ ≤ R := by
  let A := P.carrier ∩ (closure (ball (0 : E) R) \ ball 0 r)
  have hAP : A ⊆ P.carrier := inter_subset_left
  have hAb : Bornology.IsBounded A := by
    apply (isBounded_closedBall (x := (0 : E)) (r := R)).subset
    intro x hx
    exact closure_ball_subset_closedBall hx.2.1
  obtain ⟨x, hx, hfix⟩ := guo_lakshmikantham_fixed_point P hP
    (ball 0 r) (ball 0 R) isOpen_ball isOpen_ball
    (by simpa using hr)
    (by
      rw [closure_ball 0 hr.ne']
      intro x hx
      exact (mem_ball.mpr ((mem_closedBall.mp hx).trans_lt hrR)))
    isBounded_ball isBounded_ball T
    (fun x hx => hT hx.1)
    (hCC.2 A hAP hAb)
    (hCC.1.mono hAP)
    (Or.inr ⟨by
      intro x hx
      apply hexpand x hx.1
      simpa [frontier_ball (0 : E) hr.ne', mem_sphere, dist_zero_right] using hx.2,
      by
        intro x hx
        apply hcompress x hx.1
        simpa [frontier_ball (0 : E) (lt_trans hr hrR).ne', mem_sphere, dist_zero_right] using hx.2⟩)
  refine ⟨x, hx.1, hfix, ?_, ?_⟩
  · simpa [mem_ball, dist_zero_right, not_lt] using hx.2.2
  · have := closure_ball_subset_closedBall hx.2.1
    simpa [mem_closedBall, dist_zero_right] using this

/-- The old real-valued statement, without a nontriviality assumption. -/
def OriginalRealConeFixedPointPrinciple : Prop :=
  ∀ (P : Cone ℝ)
    (Ω₁ Ω₂ : Set ℝ)
    (_h_open₁ : IsOpen Ω₁) (_h_open₂ : IsOpen Ω₂)
    (_h_zero : (0 : ℝ) ∈ Ω₁)
    (_h_sub : closure Ω₁ ⊆ Ω₂)
    (_h_bounded₁ : Bornology.IsBounded Ω₁)
    (_h_bounded₂ : Bornology.IsBounded Ω₂)
    (S : ℝ → ℝ)
    (_hS_cone : MapsTo S (P.carrier ∩ (closure Ω₂ \ Ω₁)) P.carrier)
    (_hS_compact : IsCompact (closure (S '' (P.carrier ∩ (closure Ω₂ \ Ω₁)))))
    (_hS_cont : ContinuousOn S (P.carrier ∩ (closure Ω₂ \ Ω₁)))
    (_h_cond :
      ((∀ x ∈ P.carrier ∩ frontier Ω₁, ‖S x‖ ≤ ‖x‖) ∧
       (∀ x ∈ P.carrier ∩ frontier Ω₂, ‖x‖ ≤ ‖S x‖)) ∨
      ((∀ x ∈ P.carrier ∩ frontier Ω₁, ‖x‖ ≤ ‖S x‖) ∧
       (∀ x ∈ P.carrier ∩ frontier Ω₂, ‖S x‖ ≤ ‖x‖))),
    ∃ x ∈ P.carrier ∩ (closure Ω₂ \ Ω₁), S x = x

/-- The trivial cone, used only for the counterexample below. -/
def zeroConeReal : Cone ℝ where
  carrier := {0}
  nonempty := ⟨0, rfl⟩
  isClosed := isClosed_singleton
  add_mem := by intros x y hx hy; simp_all
  smul_mem := by intros c x hc hx; simp_all
  strict := by intros x hx hnx; simpa using hx

/-- The original statement is false: the cone {0} has no points in the annulus.
This proof does not use the fixed-point axiom. -/
theorem originalRealConeFixedPointPrinciple_false :
    ¬ OriginalRealConeFixedPointPrinciple := by
  intro h
  have hempty : zeroConeReal.carrier ∩
      (closure (Ioo (-2 : ℝ) 2) \ Ioo (-1 : ℝ) 1) = ∅ := by
    ext x
    simp [zeroConeReal]
  have hsub : closure (Ioo (-1 : ℝ) 1) ⊆ Ioo (-2 : ℝ) 2 := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hm : MapsTo (fun _ : ℝ => 0)
      (zeroConeReal.carrier ∩ (closure (Ioo (-2 : ℝ) 2) \ Ioo (-1 : ℝ) 1))
      zeroConeReal.carrier := by
    rw [hempty]
    exact Set.mapsTo_empty _ _
  have hc : IsCompact (closure ((fun _ : ℝ => (0 : ℝ)) ''
      (zeroConeReal.carrier ∩ (closure (Ioo (-2 : ℝ) 2) \ Ioo (-1 : ℝ) 1)))) := by
    simp [hempty]
  have ht : ContinuousOn (fun _ : ℝ => (0 : ℝ))
      (zeroConeReal.carrier ∩ (closure (Ioo (-2 : ℝ) 2) \ Ioo (-1 : ℝ) 1)) :=
    continuous_const.continuousOn
  have hcond :
      ((∀ x ∈ zeroConeReal.carrier ∩ frontier (Ioo (-1 : ℝ) 1), ‖(0 : ℝ)‖ ≤ ‖x‖) ∧
       (∀ x ∈ zeroConeReal.carrier ∩ frontier (Ioo (-2 : ℝ) 2), ‖x‖ ≤ ‖(0 : ℝ)‖)) ∨
      ((∀ x ∈ zeroConeReal.carrier ∩ frontier (Ioo (-1 : ℝ) 1), ‖x‖ ≤ ‖(0 : ℝ)‖) ∧
       (∀ x ∈ zeroConeReal.carrier ∩ frontier (Ioo (-2 : ℝ) 2), ‖(0 : ℝ)‖ ≤ ‖x‖)) := by
    left
    constructor
    · intro x _hx
      simp
    · intro x hx
      have hx0 : x = 0 := by simpa [zeroConeReal] using hx.1
      simp [hx0]
  obtain ⟨x, hx, _⟩ := h zeroConeReal (Ioo (-1) 1) (Ioo (-2) 2)
    isOpen_Ioo isOpen_Ioo (by norm_num) hsub (isBounded_Ioo (-1) 1) (isBounded_Ioo (-2) 2)
    (fun _ => 0) hm hc ht hcond
  simp [hempty] at hx

/-! ## 2. One-dimensional case -/

/-- Green function (3) for the BVP (2):

`G(t,s) = 1-t` for `0 ≤ s ≤ t ≤ 1`, and
`G(t,s) = 1-s` for `0 ≤ t ≤ s ≤ 1`.
-/
noncomputable def G1D (t s : ℝ) : ℝ :=
  if s ≤ t then 1 - t else 1 - s

/-- `G1D` is nonnegative on `[0,1] × [0,1]`. -/
lemma G1D_nonneg {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 1) :
    0 ≤ G1D t s := by
  dsimp [G1D]
  split_ifs
  · linarith [ht.2]
  · linarith [hs.2]

/-- Symmetry of the one-dimensional Green function. -/
lemma G1D_symm (t s : ℝ) : G1D t s = G1D s t := by
  unfold G1D
  split_ifs <;> linarith

/-- On the diagonal, `G(t,t)=1-t`. -/
@[simp] lemma G1D_diag (t : ℝ) : G1D t t = 1 - t := by
  simp [G1D]

/-- A continuous expression for the kernel. -/
lemma G1D_eq (t s : ℝ) : G1D t s = 1 - max t s := by
  by_cases h : s ≤ t
  · simp [G1D, h]
  · simp [G1D, h, max_eq_right (le_of_not_ge h)]

/-- Banach space `E = C([0,1],ℝ)` with the uniform norm. -/
abbrev E1D := C(Icc (0 : ℝ) 1, ℝ)

/-- Left endpoint of `[0,1]` as a subtype element. -/
def zeroPoint1D : Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩

/-- Right endpoint of `[0,1]` as a subtype element. -/
def onePoint1D : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

/-- Cone (4), written as a set. -/
def coneP1D (b : ℝ) (hb : 0 < b ∧ b < 1) : Set E1D :=
  {φ : E1D |
    (∀ t : Icc (0 : ℝ) 1, 0 ≤ φ t) ∧
    (∀ (t : ℝ) (ht : t ∈ Icc 0 b),
      (1 - b) * ‖φ‖ ≤
        φ ⟨t, ⟨by linarith [ht.1], by linarith [ht.2, hb.2]⟩⟩)}

/-- The zero function belongs to (4). -/
@[simp] theorem coneP1D_zero_mem (b : ℝ) (hb : 0 < b ∧ b < 1) :
    (0 : E1D) ∈ coneP1D b hb := by
  constructor
  · intro t
    simp
  · intro t ht
    simp

/-- In particular, the cone is nonempty. -/
theorem coneP1D_nonempty (b : ℝ) (hb : 0 < b ∧ b < 1) :
    (coneP1D b hb).Nonempty :=
  ⟨0, coneP1D_zero_mem b hb⟩

/-- Addition preserves the Harnack bound, by the triangle inequality. -/
theorem coneP1D_add_mem
    (b : ℝ) (hb : 0 < b ∧ b < 1)
    {x y : E1D}
    (hx : x ∈ coneP1D b hb) (hy : y ∈ coneP1D b hb) :
    x + y ∈ coneP1D b hb := by
  constructor
  · intro t
    change 0 ≤ x t + y t
    exact add_nonneg (hx.1 t) (hy.1 t)
  · intro t ht
    change (1 - b) * ‖x + y‖ ≤
      x ⟨t, ⟨by linarith [ht.1], by linarith [ht.2, hb.2]⟩⟩ +
      y ⟨t, ⟨by linarith [ht.1], by linarith [ht.2, hb.2]⟩⟩
    calc
      (1 - b) * ‖x + y‖ ≤ (1 - b) * (‖x‖ + ‖y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le x y) (sub_nonneg.mpr hb.2.le)
      _ = (1 - b) * ‖x‖ + (1 - b) * ‖y‖ := mul_add _ _ _
      _ ≤ _ := add_le_add (hx.2 t ht) (hy.2 t ht)

/-- Multiplication by a nonnegative scalar preserves (4). -/
theorem coneP1D_smul_mem
    (b : ℝ) (hb : 0 < b ∧ b < 1)
    {c : ℝ} {x : E1D} (hc : 0 ≤ c) (hx : x ∈ coneP1D b hb) :
    c • x ∈ coneP1D b hb := by
  constructor
  · intro t
    change 0 ≤ c * x t
    exact mul_nonneg hc (hx.1 t)
  · intro t ht
    change (1 - b) * ‖c • x‖ ≤
      c * x ⟨t, ⟨by linarith [ht.1], by linarith [ht.2, hb.2]⟩⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      (1 - b) * (c * ‖x‖) = c * ((1 - b) * ‖x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hx.2 t ht) hc

/-- Pointedness: a function and its negative can both belong only if it is zero. -/
theorem coneP1D_strict
    (b : ℝ) (hb : 0 < b ∧ b < 1)
    {x : E1D} (hx : x ∈ coneP1D b hb) (hnx : -x ∈ coneP1D b hb) :
    x = 0 := by
  ext t
  have hneg : 0 ≤ -x t := by simpa using hnx.1 t
  change x t = 0
  exact le_antisymm (neg_nonneg.mp hneg) (hx.1 t)

/-- The cone is closed in the uniform norm topology. -/
theorem coneP1D_isClosed (b : ℝ) (hb : 0 < b ∧ b < 1) :
    IsClosed (coneP1D b hb) := by
  have heq : coneP1D b hb =
      (⋂ t : Icc (0 : ℝ) 1, {φ : E1D | 0 ≤ φ t}) ∩
      (⋂ t : ℝ, ⋂ ht : t ∈ Icc 0 b,
        {φ : E1D | (1 - b) * ‖φ‖ ≤
          φ ⟨t, ⟨by linarith [ht.1], by linarith [ht.2, hb.2]⟩⟩}) := by
    ext φ
    simp [coneP1D]
  rw [heq]
  refine (isClosed_iInter fun t => ?_).inter (isClosed_iInter fun t => ?_)
  · exact isClosed_le continuous_const (continuous_eval_const t)
  · refine isClosed_iInter fun ht => ?_
    exact isClosed_le (continuous_const.mul continuous_norm)
      (continuous_eval_const
        (⟨t, ⟨by linarith [ht.1], by linarith [ht.2, hb.2]⟩⟩ : Icc (0 : ℝ) 1))

/-- Convexity follows from addition and nonnegative scalar multiplication. -/
theorem coneP1D_convex (b : ℝ) (hb : 0 < b ∧ b < 1) :
    Convex ℝ (coneP1D b hb) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a c ha hc _hac
  exact coneP1D_add_mem b hb
    (coneP1D_smul_mem b hb ha hx) (coneP1D_smul_mem b hb hc hy)

/-- The pointwise nonnegativity part of the cone definition. -/
theorem coneP1D_nonneg (b : ℝ) (hb : 0 < b ∧ b < 1)
    {φ : E1D} (hφ : φ ∈ coneP1D b hb) (t : Icc (0 : ℝ) 1) :
    0 ≤ φ t := hφ.1 t

/-- The quantitative Harnack bound on [0,b]. -/
theorem coneP1D_harnack (b : ℝ) (hb : 0 < b ∧ b < 1)
    {φ : E1D} (hφ : φ ∈ coneP1D b hb)
    (t : ℝ) (ht : t ∈ Icc 0 b) :
    (1 - b) * ‖φ‖ ≤
      φ ⟨t, ⟨by linarith [ht.1], by linarith [ht.2, hb.2]⟩⟩ := hφ.2 t ht

/-- Every nonzero cone element is strictly positive on [0,b]. -/
theorem coneP1D_pos_on_left (b : ℝ) (hb : 0 < b ∧ b < 1)
    {φ : E1D} (hφ : φ ∈ coneP1D b hb) (hne : φ ≠ 0)
    (t : ℝ) (ht : t ∈ Icc 0 b) :
    0 < φ ⟨t, ⟨by linarith [ht.1], by linarith [ht.2, hb.2]⟩⟩ := by
  exact lt_of_lt_of_le
    (mul_pos (sub_pos.mpr hb.2) (norm_pos_iff.mpr hne)) (hφ.2 t ht)

/-- Useful norm control by the value at the left endpoint. -/
theorem coneP1D_norm_le (b : ℝ) (hb : 0 < b ∧ b < 1)
    {φ : E1D} (hφ : φ ∈ coneP1D b hb) :
    ‖φ‖ ≤ φ zeroPoint1D / (1 - b) := by
  apply (le_div_iff₀ (sub_pos.mpr hb.2)).2
  simpa [zeroPoint1D, mul_comm] using hφ.2 0 ⟨le_rfl, hb.1.le⟩

/-- Cone (4) packaged for Theorem 2.1. -/
noncomputable def coneP1DCone (b : ℝ) (hb : 0 < b ∧ b < 1) : Cone E1D where
  carrier := coneP1D b hb
  nonempty := coneP1D_nonempty b hb
  isClosed := coneP1D_isClosed b hb
  add_mem := coneP1D_add_mem b hb
  smul_mem := coneP1D_smul_mem b hb
  strict := coneP1D_strict b hb

/-- Parameters occurring in the one-dimensional equation (2). -/
structure Problem1DParams where
  M : ℝ
  hM : 0 < M
  α : ℝ
  hα : 0 < α
  β : ℝ
  hβ : 0 < β
  f : ℝ → ℝ
  hf_cont : Continuous f
  hf_pos : ∀ u ≥ 0, 0 < f u
  hf_mono : MonotoneOn f (Ici 0)

/-- Continuous extension of a function on `[0,1]` to all of `ℝ` by projection. -/
noncomputable def extendE1D (φ : E1D) (s : ℝ) : ℝ :=
  φ (projIcc (0 : ℝ) 1 zero_le_one s)

/-- Denominator occurring in (5). -/
noncomputable def denominator1D (p : Problem1DParams) (φ : E1D) : ℝ :=
  (∫ s in (0 : ℝ)..1, p.f (extendE1D φ s)) ^ p.β

/-- Pointwise integral operator `S` from equation (5). -/
noncomputable def operatorS1D
    (p : Problem1DParams) (φ : E1D) (t : Icc (0 : ℝ) 1) : ℝ :=
  p.M * ∫ s in (0 : ℝ)..1,
    G1D t.1 s * ((p.f (extendE1D φ s) ^ p.α) / denominator1D p φ)

/-- Projection gives a continuous extension. -/
lemma extendE1D_continuous (φ : E1D) : Continuous (extendE1D φ) :=
  φ.continuous.comp continuous_projIcc

/-- The integral in (5) defines a continuous function of t. -/
theorem operatorS1D_continuous (p : Problem1DParams) (φ : E1D) :
    Continuous (fun t : Icc (0 : ℝ) 1 => operatorS1D p φ t) := by
  unfold operatorS1D
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ 0 1
  change Continuous (fun q : Icc (0 : ℝ) 1 × ℝ =>
    G1D q.1.1 q.2 * ((p.f (extendE1D φ q.2) ^ p.α) / denominator1D p φ))
  simp only [G1D_eq]
  exact (continuous_const.sub
    ((continuous_subtype_val.comp continuous_fst).max continuous_snd)).mul
    (((p.hf_cont.comp ((extendE1D_continuous φ).comp continuous_snd)).rpow_const
      (fun _ => Or.inr p.hα.le)).div_const _)

/-- Operator (5) as a self-map of `E1D`. -/
noncomputable def S1D (p : Problem1DParams) (φ : E1D) : E1D :=
  ⟨fun t => operatorS1D p φ t, operatorS1D_continuous p φ⟩

/-- Differential equation (2), including the two boundary conditions.

The second derivative is written using two applications of `deriv` to the projected
extension.  The equation itself is required only at interior points. -/
def IsClassicalSolution1D (p : Problem1DParams) (φ : E1D) : Prop :=
  (∀ t : ℝ, t ∈ Ioo 0 1 →
    - deriv (fun r => deriv (extendE1D φ) r) t =
      p.M * (p.f (extendE1D φ t) ^ p.α) / denominator1D p φ) ∧
  derivWithin (extendE1D φ) (Ici 0) 0 = 0 ∧
  φ onePoint1D = 0 ∧
  ContDiffOn ℝ 2 (extendE1D φ) (Icc 0 1)

/-- A zero derivative on an open interval determines a continuous function on its closure. -/
lemma constant_on_interval_of_deriv_zero {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hc : ContinuousOn f (Icc a b)) (hd : DifferentiableOn ℝ f (Ioo a b))
    (hz : ∀ t ∈ Ioo a b, deriv f t = 0) : ∀ t ∈ Icc a b, f t = f a := by
  obtain ⟨c, hconst⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo a b).isPreconnected hd (fun _ ht => hz _ ht)
  have hclosed : EqOn f (fun _ => c) (Icc a b) :=
    (show EqOn f (fun _ => c) (Ioo a b) from hconst).of_subset_closure
      hc continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  exact fun t ht => (hclosed ht).trans (hclosed ⟨le_rfl, hab.le⟩).symm

/-- C² regularity from two explicitly supplied derivatives on a closed interval. -/
lemma contDiffOn_two_of_derivatives {a b : ℝ} (hab : a < b) (f d₁ d₂ : ℝ → ℝ)
    (h₁ : ∀ t ∈ Icc a b, HasDerivAt f (d₁ t) t)
    (h₂ : ∀ t ∈ Icc a b, HasDerivAt d₁ (d₂ t) t)
    (hc₂ : ContinuousOn d₂ (Icc a b)) : ContDiffOn ℝ 2 f (Icc a b) := by
  have hu := uniqueDiffOn_Icc hab
  have hd₁ : ContDiffOn ℝ 1 d₁ (Icc a b) := by
    apply (contDiffOn_one_iff_derivWithin hu).mpr
    refine ⟨fun t ht => (h₂ t ht).differentiableAt.differentiableWithinAt, ?_⟩
    apply hc₂.congr
    intro t ht
    exact ((h₂ t ht).hasDerivWithinAt.derivWithin (hu t ht))
  rw [show (2 : ℕ∞ω) = 1+1 from rfl, contDiffOn_succ_iff_derivWithin hu]
  refine ⟨fun t ht => (h₁ t ht).differentiableAt.differentiableWithinAt, by norm_num, ?_⟩
  apply hd₁.congr
  intro t ht
  exact ((h₁ t ht).hasDerivWithinAt.derivWithin (hu t ht))

/-- The derivative within `[a,b]` agrees locally with the ordinary derivative in its interior. -/
lemma derivWithin_Icc_eventuallyEq {a b t : ℝ} (ht : t ∈ Ioo a b) (f : ℝ → ℝ) :
    derivWithin f (Icc a b) =ᶠ[𝓝 t] deriv f := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)

lemma neumann_dirichlet_unique (f : ℝ → ℝ) (hc : ContDiffOn ℝ 2 f (Icc (0 : ℝ) 1))
    (h₂ : ∀ t ∈ Ioo (0 : ℝ) 1, deriv (deriv f) t = 0)
    (h₀ : derivWithin f (Ici 0) 0 = 0) (h₁ : f 1 = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, f t = 0 := by
  let D := derivWithin f (Icc (0 : ℝ) 1)
  have hDc : ContDiffOn ℝ 1 D (Icc (0 : ℝ) 1) :=
    hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hDz : ∀ t ∈ Ioo (0 : ℝ) 1, deriv D t = 0 := by
    intro t ht
    rw [(derivWithin_Icc_eventuallyEq ht f).deriv_eq]
    exact h₂ t ht
  have hDconst := constant_on_interval_of_deriv_zero zero_lt_one D hDc.continuousOn
    ((hDc.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self) hDz
  have hD0 : D 0 = 0 := by
    have hdf := (hc.differentiableOn (by norm_num)) 0 ⟨le_rfl, zero_le_one⟩
    have hh := hdf.hasDerivWithinAt.mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 from ⟨le_rfl, zero_lt_one⟩))
    exact (hh.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans h₀
  have hdf : DifferentiableOn ℝ f (Ioo (0 : ℝ) 1) :=
    (hc.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self
  have hfconst := constant_on_interval_of_deriv_zero zero_lt_one f hc.continuousOn hdf (by
    intro t ht
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact (hDconst t (Ioo_subset_Icc_self ht)).trans hD0)
  intro t ht
  exact (hfconst t ht).trans ((hfconst 1 ⟨zero_le_one, le_rfl⟩).symm.trans h₁)

/-- A differentiable representative of the integral operator near the closed interval. -/
noncomputable def greenPrimitive1D (p : Problem1DParams) (φ : E1D) (t : ℝ) : ℝ :=
  p.M * ((1-t) * (∫ s in (0 : ℝ)..t, (p.f (extendE1D φ s)^p.α) / denominator1D p φ) +
    ∫ s in t..1, (1-s) * ((p.f (extendE1D φ s)^p.α) / denominator1D p φ))

lemma greenPrimitive1D_eq (p : Problem1DParams) (φ : E1D) (t : Icc (0 : ℝ) 1) :
    S1D p φ t = greenPrimitive1D p φ t := by
  let g := fun s => (p.f (extendE1D φ s)^p.α) / denominator1D p φ
  have hg : Continuous g := ((p.hf_cont.comp (extendE1D_continuous φ)).rpow_const
    (fun _ => Or.inr p.hα.le)).div_const _
  have hk : Continuous (fun s => G1D t s * g s) := by
    simp only [G1D_eq]; exact (continuous_const.sub (continuous_const.max continuous_id)).mul hg
  change p.M * (∫ s in (0 : ℝ)..1, G1D t s * g s) =
    p.M * ((1-t) * (∫ s in (0 : ℝ)..t, g s) + ∫ s in (t : ℝ)..1, (1-s)*g s)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hk.intervalIntegrable 0 t)
    (hk.intervalIntegrable t 1)]
  congr 2
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) t := by simpa [uIcc_of_le t.2.1] using hs
    simp [G1D, hs'.2]
  · apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (t : ℝ) 1 := by simpa [uIcc_of_le t.2.2] using hs
    change G1D t s * g s = (1-s)*g s
    rw [G1D_eq, max_eq_right hs'.1]

lemma greenPrimitive1D_derivatives (p : Problem1DParams) (φ : E1D) :
    let g := fun s => (p.f (extendE1D φ s)^p.α) / denominator1D p φ
    (∀ t, HasDerivAt (greenPrimitive1D p φ) (-p.M * ∫ s in (0 : ℝ)..t, g s) t) ∧
    (∀ t, HasDerivAt (fun t => -p.M * ∫ s in (0 : ℝ)..t, g s) (-p.M*g t) t) := by
  intro g
  have hg : Continuous g := ((p.hf_cont.comp (extendE1D_continuous φ)).rpow_const
    (fun _ => Or.inr p.hα.le)).div_const _
  have htg : Continuous (fun s => (1-s)*g s) := (continuous_const.sub continuous_id).mul hg
  have hI (t : ℝ) : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, g s) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  constructor
  · intro t
    have hJ : HasDerivAt (fun t => ∫ s in t..1, (1-s)*g s) (-((1-t)*g t)) t :=
      intervalIntegral.integral_hasDerivAt_left (htg.intervalIntegrable _ _)
        htg.aestronglyMeasurable.stronglyMeasurableAtFilter htg.continuousAt
    change HasDerivAt (fun t => p.M * ((1-t)*(∫ s in (0 : ℝ)..t, g s) +
      ∫ s in t..1, (1-s)*g s)) (-p.M * ∫ s in (0 : ℝ)..t, g s) t
    convert ((((hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)).fun_mul (hI t)).fun_add hJ).const_mul p.M using 1 <;> dsimp <;> ring
  · intro t
    exact (hI t).const_mul (-p.M)

lemma greenPrimitive1D_regular (p : Problem1DParams) (φ : E1D) :
    ContDiffOn ℝ 2 (greenPrimitive1D p φ) (Icc (0 : ℝ) 1) := by
  obtain ⟨h₁, h₂⟩ := greenPrimitive1D_derivatives p φ
  apply contDiffOn_two_of_derivatives zero_lt_one _ _ _ (fun t _ => h₁ t) (fun t _ => h₂ t)
  exact (continuous_const.mul (((p.hf_cont.comp (extendE1D_continuous φ)).rpow_const
    (fun _ => Or.inr p.hα.le)).div_const _)).continuousOn

lemma second_deriv_sub_on_interval {a b t : ℝ} (f g : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Icc a b)) (hg : ContDiffOn ℝ 2 g (Icc a b))
    (ht : t ∈ Ioo a b) :
    deriv (deriv (fun s => f s-g s)) t = deriv (deriv f) t - deriv (deriv g) t := by
  have hh := iteratedDeriv_sub (n := 2)
    ((hf t (Ioo_subset_Icc_self ht)).contDiffAt (Icc_mem_nhds ht.1 ht.2))
    ((hg t (Ioo_subset_Icc_self ht)).contDiffAt (Icc_mem_nhds ht.1 ht.2))
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.sub_def] using hh

lemma greenPrimitive1D_second_deriv (p : Problem1DParams) (φ : E1D) (t : ℝ) :
    deriv (deriv (greenPrimitive1D p φ)) t =
      -p.M * ((p.f (extendE1D φ t)^p.α) / denominator1D p φ) := by
  obtain ⟨h₁, h₂⟩ := greenPrimitive1D_derivatives p φ
  have heq : deriv (greenPrimitive1D p φ) =
      fun t => -p.M * ∫ s in (0 : ℝ)..t, (p.f (extendE1D φ s)^p.α) / denominator1D p φ :=
    funext fun t => (h₁ t).deriv
  rw [heq, (h₂ t).deriv]

/-- The differential and integral formulations of the mixed boundary problem agree. -/
theorem BVP2_iff_fixedPoint
    (p : Problem1DParams) (φ : E1D) (_hφ : ∀ t, 0 ≤ φ t) :
    IsClassicalSolution1D p φ ↔ S1D p φ = φ := by
  let u := greenPrimitive1D p φ
  have hu : ContDiffOn ℝ 2 u (Icc (0 : ℝ) 1) := greenPrimitive1D_regular p φ
  have hdu0 : HasDerivAt u 0 0 := by
    simpa only [intervalIntegral.integral_same, mul_zero] using (greenPrimitive1D_derivatives p φ).1 0
  have hu1 : u 1 = 0 := by simp [u, greenPrimitive1D]
  constructor
  · intro hclass
    let y := fun t => extendE1D φ t-u t
    have hy : ContDiffOn ℝ 2 y (Icc (0 : ℝ) 1) := hclass.2.2.2.sub hu
    have hy₂ : ∀ t ∈ Ioo (0 : ℝ) 1, deriv (deriv y) t = 0 := by
      intro t ht
      rw [second_deriv_sub_on_interval _ _ hclass.2.2.2 hu ht, greenPrimitive1D_second_deriv]
      have hh := hclass.1 t ht
      change -deriv (deriv (extendE1D φ)) t = _ at hh
      rw [mul_div_assoc] at hh
      linarith
    have hp0 : DifferentiableWithinAt ℝ (extendE1D φ) (Ici 0) 0 := by
      have hh := (hclass.2.2.2.differentiableOn (by norm_num)) 0 ⟨le_rfl, zero_le_one⟩
      exact (hh.hasDerivWithinAt.mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 from ⟨le_rfl, zero_lt_one⟩))).differentiableWithinAt
    have hy₀ : derivWithin y (Ici 0) 0 = 0 := by
      have hh := (hp0.hasDerivWithinAt.fun_sub hdu0.hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Ici 0)
      simpa only [hclass.2.1, sub_zero] using hh
    have hy₁ : y 1 = 0 := by
      have hf1 : extendE1D φ 1 = 0 := by
        rw [extendE1D, projIcc_of_mem zero_le_one (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)]
        exact hclass.2.2.1
      simp only [y, hf1, hu1, sub_self]
    have hz := neumann_dirichlet_unique y hy hy₂ hy₀ hy₁
    ext t
    have hh : extendE1D φ t = u t := sub_eq_zero.mp (hz t t.2)
    rw [greenPrimitive1D_eq]
    exact hh.symm.trans (by simp [extendE1D, projIcc_of_mem zero_le_one t.2])
  · intro hfix
    have heq : EqOn (extendE1D φ) u (Icc (0 : ℝ) 1) := by
      intro t ht
      rw [extendE1D, projIcc_of_mem zero_le_one ht]
      rw [← hfix]
      exact greenPrimitive1D_eq p φ ⟨t, ht⟩
    refine ⟨?_, ?_, ?_, hu.congr heq⟩
    · intro t ht
      have hev : extendE1D φ =ᶠ[𝓝 t] u := by
        filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
        exact heq hs
      rw [hev.deriv.deriv_eq, greenPrimitive1D_second_deriv]
      ring
    · have hev : extendE1D φ =ᶠ[𝓝[Ici 0] (0 : ℝ)] u := by
        filter_upwards [Icc_mem_nhdsGE_of_mem (show (0 : ℝ) ∈ Ico (0 : ℝ) 1 from ⟨le_rfl, zero_lt_one⟩)] with s hs
        exact heq hs
      exact (hdu0.hasDerivWithinAt.congr_of_eventuallyEq hev (heq ⟨le_rfl, zero_le_one⟩)).derivWithin
        (uniqueDiffWithinAt_Ici 0)
    · rw [← hfix]
      change p.M * (∫ s in (0 : ℝ)..1, G1D 1 s * ((p.f (extendE1D φ s)^p.α) / denominator1D p φ)) = 0
      have heq := greenPrimitive1D_eq p φ onePoint1D
      exact heq.trans hu1

/-- Pointwise kernel bounds responsible for invariance of (4). -/
lemma G1D_le_at_zero {t s : ℝ} (_ht : t ∈ Icc 0 1) (hs : s ∈ Icc 0 1) :
    G1D t s ≤ G1D 0 s := by
  simp only [G1D_eq]
  rw [max_eq_right hs.1]
  exact sub_le_sub_left (le_max_right t s) 1

lemma G1D_harnack {b t s : ℝ} (hb : 0 < b ∧ b < 1)
    (ht : t ∈ Icc 0 b) (hs : s ∈ Icc 0 1) :
    (1 - b) * G1D 0 s ≤ G1D t s := by
  rw [G1D_eq, G1D_eq, max_eq_right hs.1]
  by_cases h : s ≤ t
  · rw [max_eq_left h]
    nlinarith [ht.2, mul_nonneg (sub_nonneg.mpr hb.2.le) hs.1]
  · rw [max_eq_right (le_of_not_ge h)]
    nlinarith [mul_nonneg hb.1.le (sub_nonneg.mpr hs.2)]

/-- The cone is invariant under the integral operator. -/
theorem S1D_maps_cone (p : Problem1DParams) (b : ℝ) (hb : 0 < b ∧ b < 1)
    {φ : E1D} (hφ : ∀ t, 0 ≤ φ t) : S1D p φ ∈ coneP1D b hb := by
  let g : ℝ → ℝ := fun s => (p.f (extendE1D φ s) ^ p.α) / denominator1D p φ
  have hgcont : Continuous g :=
    ((p.hf_cont.comp (extendE1D_continuous φ)).rpow_const
      (fun _ => Or.inr p.hα.le)).div_const _
  have hden : 0 ≤ denominator1D p φ := by
    unfold denominator1D
    apply Real.rpow_nonneg
    apply intervalIntegral.integral_nonneg zero_le_one
    intro s _hs
    exact (p.hf_pos _ (hφ _)).le
  have hg : ∀ s, 0 ≤ g s := fun s =>
    div_nonneg (Real.rpow_pos_of_pos (p.hf_pos _ (hφ _)) _).le hden
  have hcont (t : ℝ) : Continuous (fun s => G1D t s * g s) := by
    simp only [G1D_eq]
    exact (continuous_const.sub (continuous_const.max continuous_id)).mul hgcont
  have hnonneg (t : Icc (0 : ℝ) 1) : 0 ≤ S1D p φ t := by
    change 0 ≤ p.M * ∫ s in (0 : ℝ)..1, G1D t.1 s * g s
    apply mul_nonneg p.hM.le
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun s hs => mul_nonneg (G1D_nonneg t.2 hs) (hg s))
  have hupper (t : Icc (0 : ℝ) 1) : S1D p φ t ≤ S1D p φ zeroPoint1D := by
    change p.M * (∫ s in (0 : ℝ)..1, G1D t.1 s * g s) ≤
      p.M * ∫ s in (0 : ℝ)..1, G1D 0 s * g s
    apply mul_le_mul_of_nonneg_left _ p.hM.le
    apply intervalIntegral.integral_mono_on zero_le_one
      ((hcont t.1).intervalIntegrable 0 1) ((hcont 0).intervalIntegrable 0 1)
    exact fun s hs => mul_le_mul_of_nonneg_right (G1D_le_at_zero t.2 hs) (hg s)
  have hnorm : ‖S1D p φ‖ ≤ S1D p φ zeroPoint1D := by
    apply (ContinuousMap.norm_le _ (hnonneg zeroPoint1D)).2
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
    exact hupper t
  constructor
  · exact hnonneg
  · intro t ht
    let tt : Icc (0 : ℝ) 1 := ⟨t, ⟨by linarith [ht.1], by linarith [ht.2, hb.2]⟩⟩
    have hlow : (1 - b) * S1D p φ zeroPoint1D ≤ S1D p φ tt := by
      change (1 - b) * (p.M * (∫ s in (0 : ℝ)..1, G1D 0 s * g s)) ≤
        p.M * ∫ s in (0 : ℝ)..1, G1D t s * g s
      rw [← mul_assoc, mul_comm (1 - b) p.M, mul_assoc,
        ← intervalIntegral.integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ p.hM.le
      apply intervalIntegral.integral_mono_on zero_le_one
        ((continuous_const.mul (hcont 0)).intervalIntegrable 0 1)
        ((hcont t).intervalIntegrable 0 1)
      intro s hs
      change (1 - b) * (G1D 0 s * g s) ≤ G1D t s * g s
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (G1D_harnack hb ht hs) (hg s)
    exact (mul_le_mul_of_nonneg_left hnorm (sub_nonneg.mpr hb.2.le)).trans hlow

/-- A uniform positive lower bound for the nonlocal denominator. -/
lemma denominator1D_lower (p : Problem1DParams) (φ : E1D)
    (hφ : ∀ t, 0 ≤ φ t) : p.f 0 ^ p.β ≤ denominator1D p φ := by
  have hi : p.f 0 ≤ ∫ s in (0 : ℝ)..1, p.f (extendE1D φ s) := by
    have hc : (∫ s in (0 : ℝ)..1, p.f 0) ≤
        ∫ s in (0 : ℝ)..1, p.f (extendE1D φ s) :=
      intervalIntegral.integral_mono_on zero_le_one
      (continuous_const.intervalIntegrable 0 1)
      ((p.hf_cont.comp (extendE1D_continuous φ)).intervalIntegrable 0 1)
      (fun s _ => p.hf_mono (show (0 : ℝ) ∈ Ici (0 : ℝ) from by simp)
        (show extendE1D φ s ∈ Ici (0 : ℝ) from hφ _) (hφ _))
    simpa using hc
  exact Real.rpow_le_rpow (p.hf_pos 0 le_rfl).le hi p.hβ.le

lemma denominator1D_pos (p : Problem1DParams) (φ : E1D)
    (hφ : ∀ t, 0 ≤ φ t) : 0 < denominator1D p φ :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (p.hf_pos 0 le_rfl) _) (denominator1D_lower p φ hφ)

/-- Continuity in the input function on the nonnegative domain. -/
theorem S1D_continuousOn (p : Problem1DParams) :
    ContinuousOn (S1D p) {φ | ∀ t, 0 ≤ φ t} := by
  let D := {φ : E1D | ∀ t, 0 ≤ φ t}
  have he : Continuous (fun q : D × ℝ => extendE1D q.1.1 q.2) := by
    have hp : Continuous (projIcc (0 : ℝ) 1 zero_le_one) := continuous_projIcc
    exact continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (hp.comp continuous_snd))
  have hi : Continuous (fun φ : D => ∫ s in (0 : ℝ)..1, p.f (extendE1D φ.1 s)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous (Function.uncurry (fun φ : D => fun s : ℝ => p.f (extendE1D φ.1 s))) from p.hf_cont.comp he) 0 1
  have hd : Continuous (fun φ : D => denominator1D p φ.1) :=
    hi.rpow_const (fun _ => Or.inr p.hβ.le)
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun q : D × Icc (0 : ℝ) 1 => operatorS1D p q.1.1 q.2)
  unfold operatorS1D
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ 0 1
  change Continuous (fun q : (D × Icc (0 : ℝ) 1) × ℝ =>
    G1D q.1.2.1 q.2 * ((p.f (extendE1D q.1.1.1 q.2) ^ p.α) /
      denominator1D p q.1.1.1))
  have he' : Continuous (fun q : (D × Icc (0 : ℝ) 1) × ℝ => extendE1D q.1.1.1 q.2) :=
    he.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  simp only [G1D_eq]
  exact (continuous_const.sub
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).max
      continuous_snd)).mul
    (((p.hf_cont.comp he').rpow_const (fun _ => Or.inr p.hα.le)).div
      (hd.comp (continuous_fst.comp continuous_fst))
      (fun q => ne_of_gt (denominator1D_pos p q.1.1.1 q.1.1.2)))

/-- Arzelà–Ascoli with a common continuous modulus supplied by a kernel. -/
lemma compact_closure_of_kernel_bound
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    (A : Set C(X, ℝ)) (k : X → Y) (hk : Continuous k)
    (C L : ℝ) (hL : 0 ≤ L)
    (hnorm : ∀ f ∈ A, ‖f‖ ≤ C)
    (hdiff : ∀ f ∈ A, ∀ x y, dist (f x) (f y) ≤ L * dist (k x) (k y)) :
    IsCompact (closure A) := by
  let H := (ContinuousMap.isometryEquivBoundedOfCompact X ℝ).toHomeomorph
  apply H.isCompact_image.mp
  rw [H.image_closure]
  apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℝ) (max C 0))
    (isCompact_closedBall _ _) (H '' A)
  · rintro f x ⟨g, hg, rfl⟩
    change dist (g x) 0 ≤ max C 0
    rw [dist_zero_right]
    exact (ContinuousMap.norm_coe_le_norm g x).trans ((hnorm g hg).trans (le_max_left _ _))
  · intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hk.continuousAt
      (ε / (L + 1)) (div_pos hε (by linarith))
    refine ⟨δ, hδ, fun x hx i => ?_⟩
    obtain ⟨g, hg, hgi⟩ := i.2
    have hkg : dist (k x₀) (k x) < ε / (L + 1) := by
      simpa [dist_comm] using hd hx
    have hsmall : L * dist (k x₀) (k x) < ε := by
      have hdist := dist_nonneg (x := k x₀) (y := k x)
      have h := (lt_div_iff₀ (show 0 < L + 1 by linarith)).mp hkg
      nlinarith
    change dist (i.1 x₀) (i.1 x) < ε
    rw [← hgi]
    exact (hdiff g hg x₀ x).trans_lt hsmall

/-- Uniform integral estimates for a continuous density. -/
lemma kernel_integral_bounds {a b M L : ℝ} (hab : a ≤ b) (hM : 0 ≤ M) (_hL : 0 ≤ L)
    (g : ℝ → ℝ) (hg : Continuous g) (hgb : ∀ s ∈ Icc a b, ‖g s‖ ≤ L)
    (u v : C(Icc a b, ℝ)) :
    ‖M * ∫ s in a..b, u (projIcc a b hab s) * g s‖ ≤ M * L * (b-a) * ‖u‖ ∧
    dist (M * ∫ s in a..b, u (projIcc a b hab s) * g s)
      (M * ∫ s in a..b, v (projIcc a b hab s) * g s) ≤
      M * L * (b-a) * dist u v := by
  have bound (w : C(Icc a b, ℝ)) :
      ‖M * ∫ s in a..b, w (projIcc a b hab s) * g s‖ ≤ M * L * (b-a) * ‖w‖ := by
    rw [norm_mul, Real.norm_of_nonneg hM]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := ‖w‖ * L) (f := fun s => w (projIcc a b hab s) * g s) (by
        intro s hs
        rw [norm_mul]
        apply mul_le_mul (ContinuousMap.norm_coe_le_norm w _)
          (hgb s (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hs)))
          (norm_nonneg _) (norm_nonneg _))
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    calc
      M * ‖∫ s in a..b, w (projIcc a b hab s) * g s‖ ≤ M * (‖w‖ * L * (b-a)) :=
        mul_le_mul_of_nonneg_left h hM
      _ = _ := by ring
  refine ⟨bound u, ?_⟩
  rw [dist_eq_norm, ← mul_sub]
  have hu : IntervalIntegrable (fun s => u (projIcc a b hab s) * g s) MeasureTheory.volume a b :=
    ((u.continuous.comp continuous_projIcc).mul hg).intervalIntegrable a b
  have hv : IntervalIntegrable (fun s => v (projIcc a b hab s) * g s) MeasureTheory.volume a b :=
    ((v.continuous.comp continuous_projIcc).mul hg).intervalIntegrable a b
  rw [← intervalIntegral.integral_sub hu hv]
  simp_rw [← sub_mul]
  simpa only [dist_eq_norm, ContinuousMap.sub_apply] using bound (u-v)

/-- Complete continuity of `S`, used in the proof of Theorem 2.2. -/
theorem S1D_completelyContinuous
    (p : Problem1DParams) :
    CompletelyContinuousOn (S1D p) {φ | ∀ t, 0 ≤ φ t} := by
  refine ⟨S1D_continuousOn p, ?_⟩
  intro A hA hbA
  obtain ⟨U, hU⟩ := hbA.exists_pos_norm_le
  let L := p.f U ^ p.α / (p.f 0 ^ p.β)
  have hL : 0 ≤ L := div_nonneg (Real.rpow_nonneg (p.hf_pos U hU.1.le).le _)
    (Real.rpow_nonneg (p.hf_pos 0 le_rfl).le _)
  let k : Icc (0 : ℝ) 1 → C(Icc (0 : ℝ) 1, ℝ) := fun t =>
    ⟨fun s => G1D t.1 s.1, by
      simp only [G1D_eq]
      exact continuous_const.sub (continuous_const.max continuous_subtype_val)⟩
  have hk : Continuous k := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 => G1D q.1.1 q.2.1)
    simp only [G1D_eq]
    exact continuous_const.sub ((continuous_subtype_val.comp continuous_fst).max
      (continuous_subtype_val.comp continuous_snd))
  have hknorm (t : Icc (0 : ℝ) 1) : ‖k t‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).2
    intro s
    change ‖G1D t.1 s.1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (G1D_nonneg t.2 s.2), G1D_eq]
    have hh : 0 ≤ max t.1 s.1 := le_trans t.2.1 (le_max_left _ _)
    linarith
  have hb (φ : E1D) (hφ : φ ∈ A) (s : ℝ) :
      ‖(p.f (extendE1D φ s) ^ p.α) / denominator1D p φ‖ ≤ L := by
    have hf0 := p.hf_pos (extendE1D φ s) (hA hφ (projIcc 0 1 zero_le_one s))
    have hfs : p.f (extendE1D φ s) ≤ p.f U := by
      apply p.hf_mono (hA hφ _) hU.1.le
      exact (le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm φ _).trans (hU.2 φ hφ))
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (Real.rpow_nonneg hf0.le _) (denominator1D_pos p φ (hA hφ)).le)]
    exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hf0.le _)
      (Real.rpow_pos_of_pos (p.hf_pos 0 le_rfl) _) (denominator1D_lower p φ (hA hφ))).trans
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow hf0.le hfs p.hα.le)
        (Real.rpow_nonneg (p.hf_pos 0 le_rfl).le _))
  have estimates (φ : E1D) (hφ : φ ∈ A) (t u : Icc (0 : ℝ) 1) :
      ‖S1D p φ t‖ ≤ p.M * L * ‖k t‖ ∧
      dist (S1D p φ t) (S1D p φ u) ≤ p.M * L * dist (k t) (k u) := by
    let g := fun s => (p.f (extendE1D φ s) ^ p.α) / denominator1D p φ
    have hg : Continuous g := ((p.hf_cont.comp (extendE1D_continuous φ)).rpow_const
      (fun _ => Or.inr p.hα.le)).div_const _
    have hh := kernel_integral_bounds zero_le_one p.hM.le hL g hg (fun s _ => hb φ hφ s) (k t) (k u)
    have heq (r : Icc (0 : ℝ) 1) :
        (∫ s in (0 : ℝ)..1, k r (projIcc 0 1 zero_le_one s) * g s) =
        ∫ s in (0 : ℝ)..1, G1D r.1 s * g s := by
      apply intervalIntegral.integral_congr
      intro s hs
      simp [k, projIcc_of_mem zero_le_one (show s ∈ Icc (0 : ℝ) 1 from by simpa using hs)]
    simpa only [heq, sub_zero, mul_one, S1D, operatorS1D, ContinuousMap.coe_mk, g] using hh
  apply compact_closure_of_kernel_bound (S1D p '' A) k hk (p.M * L) (p.M * L)
    (mul_nonneg p.hM.le hL)
  · rintro _ ⟨φ, hφ, rfl⟩
    apply (ContinuousMap.norm_le _ (mul_nonneg p.hM.le hL)).2
    intro t
    exact (estimates φ hφ t t).1.trans
      (by simpa using mul_le_mul_of_nonneg_left (hknorm t) (mul_nonneg p.hM.le hL))
  · rintro _ ⟨φ, hφ, rfl⟩ t u
    exact (estimates φ hφ t u).2

/-- Condition (a) with extended-real limsup. Using ℝ-valued limsup
without an eventual boundedness hypothesis can assign a default value
to an unbounded ratio; EReal preserves the intended +∞ case. -/
def ConditionAFormula
    (f : ℝ → ℝ) (α β M b : ℝ) : Prop :=
  Filter.limsup
      (fun u => ((((f u ^ α) / (u * (f ((1 - b) * u) ^ β))) : ℝ) : EReal))
      atTop
    < (((2 * (b ^ β)) / M : ℝ) : EReal)

/-- Condition (a) in Theorem 2.2. -/
def ConditionA1D (p : Problem1DParams) (b : ℝ) : Prop :=
  ConditionAFormula p.f p.α p.β p.M b

/-- Fixed-point formulation of a positive solution of (2).

The paper proves strict positivity on `[0,1)` and the Dirichlet value `φ(1)=0`.
-/
def IsPositiveSolution1D (p : Problem1DParams) (φ : E1D) : Prop :=
  (∀ t : Icc (0 : ℝ) 1, t.1 < 1 → 0 < φ t) ∧
  φ onePoint1D = 0 ∧
  S1D p φ = φ

/-- Boundary value at `t=1` for the integral operator. -/
@[simp] theorem S1D_at_one (p : Problem1DParams) (φ : E1D) :
    S1D p φ onePoint1D = 0 := by
  change p.M * (∫ s in (0 : ℝ)..1,
    G1D 1 s * ((p.f (extendE1D φ s) ^ p.α) / denominator1D p φ)) = 0
  have h : (∫ s in (0 : ℝ)..1,
      G1D 1 s * ((p.f (extendE1D φ s) ^ p.α) / denominator1D p φ)) =
      ∫ _s in (0 : ℝ)..1, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa using hs
    simp [G1D, hs'.2]
  rw [h]
  simp

lemma G1D_integral_at_zero : (∫ s in (0 : ℝ)..1, G1D 0 s) = 1/2 := by
  have heq : (∫ s in (0 : ℝ)..1, G1D 0 s) = ∫ s in (0 : ℝ)..1, (1-s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [G1D_eq, max_eq_right (by simpa using hs.1)]
  rw [heq, intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
    (continuous_const.intervalIntegrable 0 1)
    (continuous_id.intervalIntegrable 0 1), intervalIntegral.integral_const, integral_id]
  norm_num

/-- Sharp norm bounds using the maximum of the one-dimensional kernel at zero. -/
lemma S1D_norm_bounds (p : Problem1DParams) (φ : E1D) (hφ : ∀ t, 0 ≤ φ t)
    {l u : ℝ} (hl : 0 ≤ l)
    (hg : ∀ s ∈ Icc (0 : ℝ) 1,
      l ≤ (p.f (extendE1D φ s) ^ p.α) / denominator1D p φ ∧
      (p.f (extendE1D φ s) ^ p.α) / denominator1D p φ ≤ u) :
    p.M * l / 2 ≤ ‖S1D p φ‖ ∧ ‖S1D p φ‖ ≤ p.M * u / 2 := by
  let g := fun s => (p.f (extendE1D φ s) ^ p.α) / denominator1D p φ
  have hc : Continuous g := ((p.hf_cont.comp (extendE1D_continuous φ)).rpow_const
    (fun _ => Or.inr p.hα.le)).div_const _
  have hgc : ∀ s, 0 ≤ g s := fun s => div_nonneg
    (Real.rpow_nonneg (p.hf_pos _ (hφ _)).le _) (denominator1D_pos p φ hφ).le
  have hg0 : Continuous (fun s => G1D 0 s) := by
    simp only [G1D_eq]; exact continuous_const.sub (continuous_const.max continuous_id)
  have hgcont (t : ℝ) : Continuous (fun s => G1D t s * g s) := by
    simp only [G1D_eq]; exact (continuous_const.sub (continuous_const.max continuous_id)).mul hc
  have hlo : p.M * l / 2 ≤ S1D p φ zeroPoint1D := by
    have hi : (∫ s in (0 : ℝ)..1, G1D 0 s * l) ≤ ∫ s in (0 : ℝ)..1, G1D 0 s * g s :=
      intervalIntegral.integral_mono_on zero_le_one
        ((hg0.mul continuous_const).intervalIntegrable _ _)
        ((hgcont 0).intervalIntegrable _ _)
        (fun s hs => mul_le_mul_of_nonneg_left (hg s hs).1 (G1D_nonneg ⟨le_rfl, zero_le_one⟩ hs))
    rw [intervalIntegral.integral_mul_const, G1D_integral_at_zero] at hi
    change _ ≤ p.M * ∫ s in (0 : ℝ)..1, G1D 0 s * g s
    nlinarith [mul_le_mul_of_nonneg_left hi p.hM.le]
  have hnn (t : Icc (0 : ℝ) 1) : 0 ≤ S1D p φ t := by
    change 0 ≤ p.M * ∫ s in (0 : ℝ)..1, G1D t s * g s
    exact mul_nonneg p.hM.le (intervalIntegral.integral_nonneg zero_le_one
      (fun s hs => mul_nonneg (G1D_nonneg t.2 hs) (hgc s)))
  refine ⟨hlo.trans ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (S1D p φ) zeroPoint1D)), ?_⟩
  have hu : 0 ≤ u := hl.trans ((hg 0 ⟨le_rfl, zero_le_one⟩).1.trans (hg 0 ⟨le_rfl, zero_le_one⟩).2)
  apply (ContinuousMap.norm_le _ (div_nonneg (mul_nonneg p.hM.le hu) (by norm_num))).2
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]
  have hi : (∫ s in (0 : ℝ)..1, G1D t s * g s) ≤ ∫ s in (0 : ℝ)..1, G1D 0 s * u := by
    apply intervalIntegral.integral_mono_on zero_le_one
      ((hgcont t).intervalIntegrable _ _)
      ((hg0.mul continuous_const).intervalIntegrable _ _)
    intro s hs
    exact (mul_le_mul_of_nonneg_right (G1D_le_at_zero t.2 hs) (hgc s)).trans
      (mul_le_mul_of_nonneg_left (hg s hs).2 (G1D_nonneg ⟨le_rfl, zero_le_one⟩ hs))
  rw [intervalIntegral.integral_mul_const, G1D_integral_at_zero] at hi
  change p.M * (∫ s in (0 : ℝ)..1, G1D t s * g s) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hi p.hM.le]

lemma S1D_strictlyPositive (p : Problem1DParams) (φ : E1D) (hφ : ∀ t, 0 ≤ φ t)
    (t : Icc (0 : ℝ) 1) (ht : t.1 < 1) : 0 < S1D p φ t := by
  change 0 < p.M * ∫ s in (0 : ℝ)..1,
    G1D t s * ((p.f (extendE1D φ s) ^ p.α) / denominator1D p φ)
  apply mul_pos p.hM
  apply intervalIntegral.integral_pos zero_lt_one
  · have hc := ((p.hf_cont.comp (extendE1D_continuous φ)).rpow_const
      (fun _ => Or.inr p.hα.le)).div_const (denominator1D p φ)
    simp only [G1D_eq]
    exact ((continuous_const.sub (continuous_const.max continuous_id)).mul hc).continuousOn
  · intro s hs
    exact mul_nonneg (G1D_nonneg t.2 ⟨hs.1.le, hs.2⟩)
      (div_nonneg (Real.rpow_nonneg (p.hf_pos _ (hφ _)).le _) (denominator1D_pos p φ hφ).le)
  · refine ⟨t, t.2, ?_⟩
    rw [G1D_diag]
    exact mul_pos (sub_pos.mpr ht)
      (div_pos (Real.rpow_pos_of_pos (p.hf_pos _ (hφ _)) _) (denominator1D_pos p φ hφ))

/-- Harnack's inequality supplies the large-sphere denominator bound. -/
lemma denominator1D_cone_lower (p : Problem1DParams) (b : ℝ) (hb : 0 < b ∧ b < 1)
    (φ : E1D) (hφ : φ ∈ coneP1D b hb) :
    b ^ p.β * p.f ((1-b)*‖φ‖) ^ p.β ≤ denominator1D p φ := by
  have hc : Continuous (fun s => p.f (extendE1D φ s)) := p.hf_cont.comp (extendE1D_continuous φ)
  have hi : b * p.f ((1-b)*‖φ‖) ≤ ∫ s in (0 : ℝ)..b, p.f (extendE1D φ s) := by
    have hh : (∫ _s in (0 : ℝ)..b, p.f ((1-b)*‖φ‖)) ≤
        ∫ s in (0 : ℝ)..b, p.f (extendE1D φ s) := by
      apply intervalIntegral.integral_mono_on hb.1.le (continuous_const.intervalIntegrable 0 b)
        (hc.intervalIntegrable 0 b)
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hb.2.le⟩
      have hlow : (1-b)*‖φ‖ ≤ extendE1D φ s := by
        simpa [extendE1D, projIcc_of_mem zero_le_one hs'] using hφ.2 s hs
      exact p.hf_mono (mul_nonneg (sub_nonneg.mpr hb.2.le) (norm_nonneg _)) (hφ.1 _) hlow
    simpa using hh
  have hrest : 0 ≤ ∫ s in b..1, p.f (extendE1D φ s) :=
    intervalIntegral.integral_nonneg hb.2.le (fun s _ => (p.hf_pos _ (hφ.1 _)).le)
  have hfull : b * p.f ((1-b)*‖φ‖) ≤ ∫ s in (0 : ℝ)..1, p.f (extendE1D φ s) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 b)
      (hc.intervalIntegrable b 1)]
    linarith
  rw [← Real.mul_rpow hb.1.le (p.hf_pos _ (mul_nonneg (sub_nonneg.mpr hb.2.le) (norm_nonneg _))).le]
  exact Real.rpow_le_rpow (mul_nonneg hb.1.le
    (p.hf_pos _ (mul_nonneg (sub_nonneg.mpr hb.2.le) (norm_nonneg _))).le) hfull p.hβ.le

lemma denominator1D_upper (p : Problem1DParams) (φ : E1D) (hφ : ∀ t, 0 ≤ φ t)
    {R : ℝ} (hR : 0 ≤ R) (hnorm : ‖φ‖ ≤ R) : denominator1D p φ ≤ p.f R ^ p.β := by
  have hc : Continuous (fun s => p.f (extendE1D φ s)) := p.hf_cont.comp (extendE1D_continuous φ)
  have hi : (∫ s in (0 : ℝ)..1, p.f (extendE1D φ s)) ≤ ∫ _s in (0 : ℝ)..1, p.f R := by
    apply intervalIntegral.integral_mono_on zero_le_one
      (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    intro s _
    apply p.hf_mono (hφ _) hR
    exact (le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm φ _).trans hnorm)
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hi
  exact Real.rpow_le_rpow
    (intervalIntegral.integral_nonneg zero_le_one (fun s _ => (p.hf_pos _ (hφ _)).le)) hi p.hβ.le

/-- Theorem 2.2, using only the cone fixed-point principle as a custom axiom. -/
theorem existence_1D
    (p : Problem1DParams)
    (b : ℝ) (hb : 0 < b ∧ b < 1)
    (hA : ConditionA1D p b) :
    ∃ φ : E1D, IsPositiveSolution1D p φ := by
  let l := p.f 0 ^ p.α / p.f 1 ^ p.β
  have hl : 0 < l := div_pos (Real.rpow_pos_of_pos (p.hf_pos 0 le_rfl) _)
    (Real.rpow_pos_of_pos (p.hf_pos 1 zero_le_one) _)
  let r := min 1 (p.M*l/4)
  have hr : 0 < r := lt_min zero_lt_one (div_pos (mul_pos p.hM hl) (by norm_num))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrlo : r ≤ p.M*l/2 := (min_le_right _ _).trans (by nlinarith [mul_pos p.hM hl])
  have hlarge : ∀ᶠ u : ℝ in atTop,
      (p.f u ^ p.α) / (u * (p.f ((1-b)*u) ^ p.β)) < 2*b^p.β/p.M := by
    exact (eventually_lt_of_limsup_lt hA).mono fun u hu => EReal.coe_lt_coe_iff.mp hu
  obtain ⟨U, hU⟩ := eventually_atTop.mp hlarge
  let R := max U (r+1)
  have hrR : r < R := lt_of_lt_of_le (by linarith : r < r+1) (le_max_right _ _)
  have hR : 0 < R := lt_trans hr hrR
  have hRat := hU R (le_max_left _ _)
  have hP : ∃ φ ∈ (coneP1DCone b hb).carrier, φ ≠ 0 := by
    let φ : E1D := ContinuousMap.const _ 1
    have hn : ‖φ‖ ≤ 1 := (ContinuousMap.norm_le _ (by norm_num)).2 (by intro t; norm_num [φ])
    refine ⟨φ, ⟨by intro t; norm_num [φ], ?_⟩, ?_⟩
    · intro t ht
      change (1-b)*‖φ‖ ≤ 1
      nlinarith [norm_nonneg φ, hb.1]
    · intro heq
      have hh := congrArg (fun ψ : E1D => ψ zeroPoint1D) heq
      norm_num [φ] at hh
  have hCC : CompletelyContinuousOn (S1D p) (coneP1DCone b hb).carrier :=
    ⟨(S1D_completelyContinuous p).1.mono (fun _ h => h.1),
      fun A hA hB => (S1D_completelyContinuous p).2 A (fun _ h => (hA h).1) hB⟩
  obtain ⟨φ, hφ, hfix, _⟩ := cone_fixedPoint_between_spheres (coneP1DCone b hb) hP (S1D p)
    (fun φ hφ => S1D_maps_cone p b hb hφ.1) hCC hr hrR
    (by
      intro φ hφ hn
      have hdenup := denominator1D_upper p φ hφ.1 zero_le_one (hn.le.trans hr1)
      have hd1 : 0 < p.f 1 ^ p.β := Real.rpow_pos_of_pos (p.hf_pos 1 zero_le_one) _
      have hbounds : ∀ s ∈ Icc (0 : ℝ) 1,
          l ≤ (p.f (extendE1D φ s) ^ p.α) / denominator1D p φ ∧
          (p.f (extendE1D φ s) ^ p.α) / denominator1D p φ ≤
            p.f 1 ^ p.α / p.f 0 ^ p.β := by
        intro s hs
        have hs0 := hφ.1 (projIcc 0 1 zero_le_one s)
        have hfs := p.hf_mono hs0 (show (1 : ℝ) ∈ Ici (0 : ℝ) from by norm_num)
          ((le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm φ _).trans (hn.le.trans hr1)))
        have hf0 := p.hf_mono (show (0 : ℝ) ∈ Ici (0 : ℝ) from by simp) hs0 hs0
        refine ⟨?_, ?_⟩
        · exact (div_le_div_of_nonneg_right
            (Real.rpow_le_rpow (p.hf_pos 0 le_rfl).le hf0 p.hα.le) hd1.le).trans
            (div_le_div_of_nonneg_left (Real.rpow_nonneg (p.hf_pos _ hs0).le _)
              (denominator1D_pos p φ hφ.1) hdenup)
        · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (p.hf_pos _ hs0).le _)
            (Real.rpow_pos_of_pos (p.hf_pos 0 le_rfl) _) (denominator1D_lower p φ hφ.1)).trans
            (div_le_div_of_nonneg_right (Real.rpow_le_rpow (p.hf_pos _ hs0).le hfs p.hα.le)
              (Real.rpow_nonneg (p.hf_pos 0 le_rfl).le _))
      rw [hn]
      exact hrlo.trans (S1D_norm_bounds p φ hφ.1 hl.le hbounds).1)
    (by
      intro φ hφ hn
      let d := b^p.β * p.f ((1-b)*R)^p.β
      have hcR : 0 < (1-b)*R := mul_pos (sub_pos.mpr hb.2) hR
      have hfb : 0 < p.f ((1-b)*R)^p.β := Real.rpow_pos_of_pos (p.hf_pos _ hcR.le) _
      have hd : 0 < d := mul_pos (Real.rpow_pos_of_pos hb.1 _) hfb
      have hden : d ≤ denominator1D p φ := by simpa only [hn] using denominator1D_cone_lower p b hb φ hφ
      have hbounds : ∀ s ∈ Icc (0 : ℝ) 1,
          0 ≤ (p.f (extendE1D φ s) ^ p.α) / denominator1D p φ ∧
          (p.f (extendE1D φ s) ^ p.α) / denominator1D p φ ≤ p.f R ^ p.α / d := by
        intro s hs
        have hs0 := hφ.1 (projIcc 0 1 zero_le_one s)
        have hfs := p.hf_mono hs0 hR.le
          ((le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm φ _).trans hn.le))
        refine ⟨div_nonneg (Real.rpow_nonneg (p.hf_pos _ hs0).le _) (denominator1D_pos p φ hφ.1).le, ?_⟩
        exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (p.hf_pos _ hs0).le _) hd hden).trans
          (div_le_div_of_nonneg_right (Real.rpow_le_rpow (p.hf_pos _ hs0).le hfs p.hα.le) hd.le)
      have hnum : p.M * p.f R ^ p.α < (2*b^p.β)*(R*p.f ((1-b)*R)^p.β) :=
        by simpa only [mul_comm (p.f R ^ p.α) p.M] using
          (div_lt_div_iff₀ (mul_pos hR hfb) p.hM).mp hRat
      have hbound : p.M * (p.f R ^ p.α / d) / 2 ≤ R := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), ← mul_div_assoc, div_le_iff₀ hd]
        dsimp [d]
        nlinarith
      exact (S1D_norm_bounds p φ hφ.1 (le_refl 0) hbounds).2.trans (by simpa only [hn] using hbound))
  refine ⟨φ, ?_, ?_, hfix⟩
  · intro t ht
    rw [← hfix]
    exact S1D_strictlyPositive p φ hφ.1 t ht
  · rw [← hfix]
    exact S1D_at_one p φ

/-! ### The three examples after Theorem 2.2 -/

/-- The nonlinearity used in Example 1. -/
noncomputable def powerPlusEps (σ ε u : ℝ) : ℝ := u ^ σ + ε

/-- The explicit sufficient asymptotic inequality printed in Example 1. -/
def Example1AsymptoticCondition
    (α β M b σ : ℝ) : Prop :=
  Filter.limsup (fun u : ℝ => ((u ^ (σ * (α - β) - 1) : ℝ) : EReal)) atTop
    < ((((2 * (b ^ β)) / M) * ((1 - b) ^ (σ * β)) : ℝ) : EReal)

lemma powerPlusEps_ratio_factorization {u c σ ε α β : ℝ}
    (hu : 0 < u) (hc : 0 < c) (hε : 0 < ε) :
    (u ^ σ + ε) ^ α / (u * ((c * u) ^ σ + ε) ^ β) =
      u ^ (σ * (α - β) - 1) *
        ((1 + ε / u ^ σ) ^ α / (c ^ σ + ε / u ^ σ) ^ β) := by
  have hbase : 0 < u ^ σ := Real.rpow_pos_of_pos hu _
  have hN : 0 < 1 + ε / u ^ σ := by positivity
  have hD : 0 < c ^ σ + ε / u ^ σ := by positivity
  have hn : u ^ σ + ε = u ^ σ * (1 + ε / u ^ σ) := by field_simp
  have hd : (c * u) ^ σ + ε = u ^ σ * (c ^ σ + ε / u ^ σ) := by
    rw [Real.mul_rpow hc.le hu.le]
    field_simp
  rw [hn, hd, Real.mul_rpow hbase.le hN.le, Real.mul_rpow hbase.le hD.le]
  rw [Real.rpow_sub hu (σ * (α - β)) 1, Real.rpow_one]
  have he : σ * (α - β) = σ * α - σ * β := by ring
  rw [he, Real.rpow_sub hu (σ * α) (σ * β), Real.rpow_mul hu.le σ α,
    Real.rpow_mul hu.le σ β]
  field_simp

/-- The complete asymptotic proof for Example 1. -/
theorem example1_conditionA (α β M b σ ε : ℝ)
    (_hα : 0 < α) (_hβ : 0 < β) (hM : 0 < M)
    (hb : 0 < b ∧ b < 1) (hσ : 0 < σ) (hε : 0 < ε)
    (h : Example1AsymptoticCondition α β M b σ) :
    ConditionAFormula (powerPlusEps σ ε) α β M b := by
  let c : ℝ := 1 - b
  let e : ℝ := σ * (α - β) - 1
  have hc : 0 < c := sub_pos.mpr hb.2
  have hsmall : Tendsto (fun u : ℝ => ε / u ^ σ) atTop (𝓝 0) :=
    (tendsto_rpow_atTop hσ).const_div_atTop ε
  have hN : Tendsto (fun u : ℝ => 1 + ε / u ^ σ) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hsmall
  have hD : Tendsto (fun u : ℝ => c ^ σ + ε / u ^ σ) atTop (𝓝 (c ^ σ)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => c ^ σ) atTop (𝓝 (c ^ σ))).add hsmall
  have hcσ : 0 < c ^ σ := Real.rpow_pos_of_pos hc _
  have hQ : Tendsto (fun u : ℝ =>
      (1 + ε / u ^ σ) ^ α / (c ^ σ + ε / u ^ σ) ^ β)
      atTop (𝓝 (1 / (c ^ σ) ^ β)) := by
    simpa only [Pi.div_def, Real.one_rpow] using (hN.rpow_const (Or.inl one_ne_zero)).div
      (hD.rpow_const (Or.inl hcσ.ne')) (Real.rpow_pos_of_pos hcσ β).ne'
  have he : e ≤ 0 := by
    by_contra hn
    have hp : 0 < e := lt_of_not_ge hn
    have ht : Tendsto (fun u : ℝ => ((u ^ e : ℝ) : EReal)) atTop (𝓝 ⊤) :=
      EReal.tendsto_coe_nhds_top_iff.mpr (tendsto_rpow_atTop hp)
    change Filter.limsup (fun u : ℝ => ((u ^ e : ℝ) : EReal)) atTop < _ at h
    rw [ht.limsup_eq] at h
    exact not_lt_of_ge le_top h
  have hlim (L : ℝ) (hp : Tendsto (fun u : ℝ => u ^ e) atTop (𝓝 L)) :
      Tendsto (fun u : ℝ =>
        ((powerPlusEps σ ε u ^ α /
          (u * powerPlusEps σ ε (c * u) ^ β) : ℝ) : EReal))
        atTop (𝓝 ((L * (1 / (c ^ σ) ^ β) : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.mpr
    apply (hp.mul hQ).congr'
    filter_upwards [eventually_gt_atTop 0] with u hu
    exact (powerPlusEps_ratio_factorization hu hc hε).symm
  by_cases hneg : e < 0
  · have hp : Tendsto (fun u : ℝ => u ^ e) atTop (𝓝 0) := by
      simpa using tendsto_rpow_neg_atTop (neg_pos.mpr hneg)
    have hlimE := hlim 0 hp
    unfold ConditionAFormula
    change Filter.limsup (fun u : ℝ =>
      ((powerPlusEps σ ε u ^ α / (u * powerPlusEps σ ε (c * u) ^ β) : ℝ) : EReal)) atTop < _
    rw [hlimE.limsup_eq]
    simp only [zero_mul, EReal.coe_zero]
    exact_mod_cast div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hb.1 _)) hM
  · have he0 : e = 0 := le_antisymm he (le_of_not_gt hneg)
    have hp : Tendsto (fun u : ℝ => u ^ e) atTop (𝓝 1) := by
      simp [he0]
    have hlimE := hlim 1 hp
    have hcrit : (1 : ℝ) < ((2 * b ^ β) / M) * (c ^ (σ * β)) := by
      have h' : (1 : EReal) < (((2 * b ^ β) / M * c ^ (σ * β) : ℝ) : EReal) := by
        change Filter.limsup (fun u : ℝ => ((u ^ e : ℝ) : EReal)) atTop <
          (((2 * b ^ β) / M * c ^ (σ * β) : ℝ) : EReal) at h
        simpa [he0] using h
      exact_mod_cast h'
    have hbound : 1 / (c ^ σ) ^ β < (2 * b ^ β) / M := by
      rw [← Real.rpow_mul hc.le σ β]
      exact (div_lt_iff₀ (Real.rpow_pos_of_pos hc _)).2 hcrit
    unfold ConditionAFormula
    change Filter.limsup (fun u : ℝ =>
      ((powerPlusEps σ ε u ^ α / (u * powerPlusEps σ ε (c * u) ^ β) : ℝ) : EReal)) atTop < _
    rw [hlimE.limsup_eq]
    simpa only [one_mul] using (EReal.coe_lt_coe_iff.mpr hbound)

/-- Example 2: for `f(u)=exp(u)`, condition (a) is asserted when `α<β` and
`1-b=α/β`. -/
theorem example2_exp_conditionA (α β M b : ℝ)
    (_hα : 0 < α) (hβ : 0 < β) (_hαβ : α < β)
    (hM : 0 < M) (hb : 0 < b ∧ b < 1) (hbchoice : 1 - b = α / β) :
    ConditionAFormula Real.exp α β M b := by
  have hab : (1 - b) * β = α := (eq_div_iff hβ.ne').mp hbchoice
  have heq (u : ℝ) : (Real.exp u ^ α) /
      (u * (Real.exp ((1 - b) * u) ^ β)) = u⁻¹ := by
    rw [← Real.exp_mul, ← Real.exp_mul]
    have he : ((1 - b) * u) * β = u * α := by
      calc
        _ = u * ((1 - b) * β) := by ring
        _ = u * α := by rw [hab]
    rw [he]
    by_cases hu : u = 0
    · simp [hu]
    · field_simp [Real.exp_ne_zero, hu]
  have ht : Tendsto (fun u : ℝ => ((u⁻¹ : ℝ) : EReal)) atTop (𝓝 (0 : EReal)) := by
    exact EReal.tendsto_coe.mpr (tendsto_inv_atTop_zero (𝕜 := ℝ))
  unfold ConditionAFormula
  simp only [heq]
  rw [ht.limsup_eq]
  exact_mod_cast div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hb.1 _)) hM

/-- Example 3, recorded exactly as an asymptotic claim from the paper.

The printed example uses `f(u)=ln(u)`.  Since `ln(0)` is not positive, this example
cannot directly instantiate `Problem1DParams`, whose global assumptions include
positivity on all `u≥0`.  We therefore formalize only the condition-(a) claim itself,
without silently changing the paper's `ln(u)` to another function.
-/
theorem example3_log_conditionA (α β M b : ℝ)
    (_hα : 0 < α) (_hβ : 0 < β) (hM : 0 < M) (hb : 0 < b ∧ b < 1) :
    ConditionAFormula Real.log α β M b := by
  let c : ℝ := 1 - b
  have hc : 0 < c := sub_pos.mpr hb.2
  have hlogc : Tendsto (fun u : ℝ => Real.log (c * u)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop hc)
  have hq : Tendsto (fun u : ℝ => Real.log u / Real.log (c * u)) atTop (𝓝 1) := by
    have hh' : Tendsto (fun u : ℝ => 1 - Real.log c / Real.log (c * u)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
        (hlogc.const_div_atTop (Real.log c))
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop 0, hlogc.eventually_gt_atTop 0] with u hu hlu
    have he : Real.log (c * u) = Real.log c + Real.log u := Real.log_mul hc.ne' hu.ne'
    field_simp [hlu.ne']
    linarith [he]
  have hpow : Tendsto (fun u : ℝ => Real.log u ^ (α - β) / u) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_rpow_atTop (α - β) (s := 1) zero_lt_one).tendsto_div_nhds_zero
  have hprod : Tendsto (fun u : ℝ =>
      (Real.log u ^ (α - β) / u) * (Real.log u / Real.log (c * u)) ^ β) atTop (𝓝 0) := by
    simpa using hpow.mul (hq.rpow_const (Or.inl one_ne_zero))
  have hlim : Tendsto (fun u : ℝ => Real.log u ^ α / (u * Real.log (c * u) ^ β))
      atTop (𝓝 0) := by
    apply hprod.congr'
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,
      hlogc.eventually_gt_atTop 0, eventually_gt_atTop 0] with u hlu hlcu hu
    rw [Real.rpow_sub hlu α β, Real.div_rpow hlu.le hlcu.le β]
    field_simp [(Real.rpow_pos_of_pos hlu β).ne', (Real.rpow_pos_of_pos hlcu β).ne', hu.ne']
  have hlimE : Tendsto (fun u : ℝ =>
      ((Real.log u ^ α / (u * Real.log (c * u) ^ β) : ℝ) : EReal)) atTop (𝓝 0) :=
    EReal.tendsto_coe.mpr hlim
  unfold ConditionAFormula
  change Filter.limsup (fun u : ℝ =>
    ((Real.log u ^ α / (u * Real.log (c * u) ^ β) : ℝ) : EReal)) atTop < _
  rw [hlimE.limsup_eq]
  exact_mod_cast div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hb.1 _)) hM

/-! ## 3. Radial problem in an annulus -/

/-- Parameters for the annulus problem (11)–(15).

`pn` represents the paper's `p_n`, the `(n-1)`-dimensional measure of the unit
sphere in `ℝⁿ`.  The paper does not need an explicit Gamma-function formula for it,
so it is kept as a positive parameter here.
-/
structure AnnulusParams where
  n : ℕ
  hn : 3 ≤ n
  a : ℝ
  b : ℝ
  hab : 0 < a ∧ a < b
  pn : ℝ
  hpn : 0 < pn
  M : ℝ
  hM : 0 < M
  α : ℝ
  hα : 0 < α
  β : ℝ
  hβ : 0 < β
  f : ℝ → ℝ
  hf_cont : Continuous f
  hf_pos : ∀ u ≥ 0, 0 < f u
  hf_mono : MonotoneOn f (Ici 0)

/-- `A(t)=(a/t)^(n-2)` in formula (13). -/
noncomputable def A_radial (p : AnnulusParams) (t : ℝ) : ℝ :=
  (p.a / t) ^ ((p.n : ℝ) - 2)

/-- `B(t)=(b/t)^(n-2)` in formula (13). -/
noncomputable def B_radial (p : AnnulusParams) (t : ℝ) : ℝ :=
  (p.b / t) ^ ((p.n : ℝ) - 2)

/-- Green function for the radial annulus problem, with corrected sign.

The printed (13) uses A'(s)-B'(s), which is positive, while the
numerator is negative in the interior. For the operator -Δ the
positive Green function uses B'(s)-A'(s). This corrects that sign. -/
noncomputable def G_annulus (p : AnnulusParams) (t s : ℝ) : ℝ :=
  let W := deriv (B_radial p) s - deriv (A_radial p) s
  if s ≤ t then
    (1 - B_radial p t) * (1 - A_radial p s) / W
  else
    (1 - A_radial p t) * (1 - B_radial p s) / W

/-- The paper states that the annulus Green function is positive away from the
Dirichlet endpoints, and nonnegative on the closed square. -/
lemma deriv_radial_power {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (k : ℝ) :
    deriv (fun t : ℝ => (c / t) ^ k) s = -k * (c / s) ^ k / s := by
  have hd : HasDerivAt (fun t : ℝ => c / t) (-c / s ^ 2) s := by
    simpa using (hasDerivAt_const s c).fun_div (hasDerivAt_id s) hs.ne'
  rw [(hd.rpow_const (Or.inl (div_ne_zero hc.ne' hs.ne'))).deriv]
  rw [Real.rpow_sub (div_pos hc hs) k 1, Real.rpow_one]
  field_simp

lemma radial_exponent_pos (p : AnnulusParams) : 0 < (p.n : ℝ) - 2 := by
  have hn : (3 : ℝ) ≤ p.n := by exact_mod_cast p.hn
  linarith

lemma radial_wronskian_neg (p : AnnulusParams) {s : ℝ} (hs : 0 < s) :
    deriv (B_radial p) s - deriv (A_radial p) s < 0 := by
  have hb : 0 < p.b := lt_trans p.hab.1 p.hab.2
  have hAB : (p.a / s) ^ ((p.n : ℝ) - 2) < (p.b / s) ^ ((p.n : ℝ) - 2) :=
    Real.rpow_lt_rpow (div_nonneg p.hab.1.le hs.le)
      ((div_lt_div_iff_of_pos_right hs).2 p.hab.2) (radial_exponent_pos p)
  unfold A_radial B_radial
  rw [deriv_radial_power hb hs, deriv_radial_power p.hab.1 hs, ← sub_div]
  apply div_neg_of_neg_of_pos _ hs
  nlinarith [mul_pos (radial_exponent_pos p) (sub_pos.mpr hAB)]

lemma A_radial_le_one (p : AnnulusParams) {t : ℝ} (ht : t ∈ Icc p.a p.b) :
    A_radial p t ≤ 1 := by
  have htpos := lt_of_lt_of_le p.hab.1 ht.1
  exact Real.rpow_le_one (div_nonneg p.hab.1.le htpos.le)
    ((div_le_one htpos).2 ht.1) (radial_exponent_pos p).le

lemma one_le_B_radial (p : AnnulusParams) {t : ℝ} (ht : t ∈ Icc p.a p.b) :
    1 ≤ B_radial p t := by
  have htpos := lt_of_lt_of_le p.hab.1 ht.1
  exact Real.one_le_rpow ((one_le_div htpos).2 ht.2) (radial_exponent_pos p).le

theorem G_annulus_nonneg (p : AnnulusParams) {t s : ℝ}
    (ht : t ∈ Icc p.a p.b) (hs : s ∈ Icc p.a p.b) :
    0 ≤ G_annulus p t s := by
  have hW := (radial_wronskian_neg p (lt_of_lt_of_le p.hab.1 hs.1)).le
  unfold G_annulus
  dsimp
  split_ifs
  · apply div_nonneg_of_nonpos
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (one_le_B_radial p ht))
        (sub_nonneg.mpr (A_radial_le_one p hs))
    · exact hW
  · apply div_nonneg_of_nonpos
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (A_radial_le_one p ht))
        (sub_nonpos.mpr (one_le_B_radial p hs))
    · exact hW

/-- A min/max expression removes the branch from the radial kernel. -/
lemma G_annulus_eq (p : AnnulusParams) (t s : ℝ) :
    G_annulus p t s = (1 - B_radial p (max t s)) * (1 - A_radial p (min t s)) /
      (deriv (B_radial p) s - deriv (A_radial p) s) := by
  by_cases h : s ≤ t
  · simp [G_annulus, h]
  · simp [G_annulus, h, max_eq_right (le_of_not_ge h), min_eq_left (le_of_not_ge h), mul_comm]

lemma G_annulus_continuous (p : AnnulusParams) :
    Continuous (fun q : Icc p.a p.b × Icc p.a p.b => G_annulus p q.1 q.2) := by
  let k : ℝ := (p.n : ℝ) - 2
  have ht : Continuous (fun q : Icc p.a p.b × Icc p.a p.b => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hs : Continuous (fun q : Icc p.a p.b × Icc p.a p.b => (q.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hmin (q : Icc p.a p.b × Icc p.a p.b) : 0 < min (q.1 : ℝ) (q.2 : ℝ) :=
    lt_min (lt_of_lt_of_le p.hab.1 q.1.2.1) (lt_of_lt_of_le p.hab.1 q.2.2.1)
  have hmax (q : Icc p.a p.b × Icc p.a p.b) : 0 < max (q.1 : ℝ) (q.2 : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le p.hab.1 q.1.2.1) (le_max_left _ _)
  have hA : Continuous (fun q : Icc p.a p.b × Icc p.a p.b => A_radial p (min (q.1 : ℝ) q.2)) :=
    (continuous_const.div (ht.min hs) (fun q => (hmin q).ne')).rpow_const
      (fun _ => Or.inr (radial_exponent_pos p).le)
  have hB : Continuous (fun q : Icc p.a p.b × Icc p.a p.b => B_radial p (max (q.1 : ℝ) q.2)) :=
    (continuous_const.div (ht.max hs) (fun q => (hmax q).ne')).rpow_const
      (fun _ => Or.inr (radial_exponent_pos p).le)
  have hAs : Continuous (fun q : Icc p.a p.b × Icc p.a p.b => A_radial p q.2) :=
    (continuous_const.div hs (fun q => (lt_of_lt_of_le p.hab.1 q.2.2.1).ne')).rpow_const
      (fun _ => Or.inr (radial_exponent_pos p).le)
  have hBs : Continuous (fun q : Icc p.a p.b × Icc p.a p.b => B_radial p q.2) :=
    (continuous_const.div hs (fun q => (lt_of_lt_of_le p.hab.1 q.2.2.1).ne')).rpow_const
      (fun _ => Or.inr (radial_exponent_pos p).le)
  have hW : Continuous (fun q : Icc p.a p.b × Icc p.a p.b =>
      deriv (B_radial p) q.2 - deriv (A_radial p) q.2) := by
    have heq (q : Icc p.a p.b × Icc p.a p.b) :
        deriv (B_radial p) q.2 - deriv (A_radial p) q.2 =
        (-k * B_radial p q.2 / q.2) - (-k * A_radial p q.2 / q.2) := by
      unfold A_radial B_radial
      rw [deriv_radial_power (lt_trans p.hab.1 p.hab.2) (lt_of_lt_of_le p.hab.1 q.2.2.1),
        deriv_radial_power p.hab.1 (lt_of_lt_of_le p.hab.1 q.2.2.1)]
    simp_rw [heq]
    exact ((continuous_const.mul hBs).div hs
      (fun q => (lt_of_lt_of_le p.hab.1 q.2.2.1).ne')).sub
      ((continuous_const.mul hAs).div hs (fun q => (lt_of_lt_of_le p.hab.1 q.2.2.1).ne'))
  simp_rw [G_annulus_eq]
  exact ((continuous_const.sub hB).mul (continuous_const.sub hA)).div hW
    (fun q => (radial_wronskian_neg p (lt_of_lt_of_le p.hab.1 q.2.2.1)).ne)

/-- Constant `c` immediately before equation (14). -/
noncomputable def c_annulus (p : AnnulusParams) (a₁ b₁ : ℝ) : ℝ :=
  let n_exp := (p.n : ℝ) - 2
  let num := min ((p.b / b₁) ^ n_exp - 1)
                 (1 - (p.a / a₁) ^ n_exp)
  let den := max ((p.b / p.a) ^ n_exp - 1)
                 (1 - (p.a / p.b) ^ n_exp)
  num / den

/-- The paper's geometric choice implies `0<c<1`. -/
theorem c_annulus_bounds (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) :
    0 < c_annulus p a₁ b₁ ∧ c_annulus p a₁ b₁ < 1 := by
  have hk : 0 < (p.n : ℝ) - 2 := by
    have hn : (3 : ℝ) ≤ p.n := by exact_mod_cast p.hn
    linarith
  have ha₁ : 0 < a₁ := lt_trans p.hab.1 h.1
  have hb₁ : 0 < b₁ := lt_trans ha₁ h.2.1
  have ha_b₁ : p.a < b₁ := lt_trans h.1 h.2.1
  have hU : 0 < (p.b / b₁) ^ ((p.n : ℝ) - 2) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow ((one_lt_div hb₁).2 h.2.2) hk)
  have hV : 0 < 1 - (p.a / a₁) ^ ((p.n : ℝ) - 2) :=
    sub_pos.mpr (Real.rpow_lt_one (div_nonneg p.hab.1.le ha₁.le)
      ((div_lt_one ha₁).2 h.1) hk)
  have hD : 0 < (p.b / p.a) ^ ((p.n : ℝ) - 2) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow ((one_lt_div p.hab.1).2 p.hab.2) hk)
  have hlt : (p.b / b₁) ^ ((p.n : ℝ) - 2) - 1 <
      (p.b / p.a) ^ ((p.n : ℝ) - 2) - 1 := by
    apply sub_lt_sub_right
    apply Real.rpow_lt_rpow (div_nonneg (lt_trans p.hab.1 p.hab.2).le hb₁.le) _ hk
    exact div_lt_div_of_pos_left (lt_trans p.hab.1 p.hab.2) p.hab.1 ha_b₁
  unfold c_annulus
  dsimp
  have hden : 0 < max ((p.b / p.a) ^ ((p.n : ℝ) - 2) - 1)
      (1 - (p.a / p.b) ^ ((p.n : ℝ) - 2)) := lt_of_lt_of_le hD (le_max_left _ _)
  constructor
  · exact div_pos (lt_min hU hV) hden
  · apply (div_lt_one hden).2
    exact lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le hlt (le_max_left _ _))

/-- Banach space `E=C([a,b],ℝ)` in Section 3. -/
abbrev EAnnulus (p : AnnulusParams) := C(Icc p.a p.b, ℝ)

/-- Left endpoint of the annulus interval. -/
def leftPointAnnulus (p : AnnulusParams) : Icc p.a p.b :=
  ⟨p.a, le_rfl, p.hab.2.le⟩

/-- Right endpoint of the annulus interval. -/
def rightPointAnnulus (p : AnnulusParams) : Icc p.a p.b :=
  ⟨p.b, p.hab.2.le, le_rfl⟩

/-- Cone (15), as a set. -/
def conePAnnulus
    (p : AnnulusParams)
    (a₁ b₁ : ℝ)
    (ha₁b₁ : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) :
    Set (EAnnulus p) :=
  {φ : EAnnulus p |
    (∀ t : Icc p.a p.b, 0 ≤ φ t) ∧
    (∀ (t : ℝ) (ht : t ∈ Icc a₁ b₁),
      c_annulus p a₁ b₁ * ‖φ‖ ≤
        φ ⟨t, ⟨by linarith [p.hab.1, ha₁b₁.1, ht.1],
                 by linarith [ha₁b₁.2.2, ht.2]⟩⟩)}

/-- All structural properties of the annulus cone are proved below. -/
@[simp] theorem conePAnnulus_zero_mem (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) :
    (0 : EAnnulus p) ∈ conePAnnulus p a₁ b₁ h := by
  constructor <;> intros <;> simp

theorem conePAnnulus_nonempty (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) :
    (conePAnnulus p a₁ b₁ h).Nonempty := ⟨0, conePAnnulus_zero_mem p a₁ b₁ h⟩

theorem conePAnnulus_add_mem (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) {x y : EAnnulus p}
    (hx : x ∈ conePAnnulus p a₁ b₁ h) (hy : y ∈ conePAnnulus p a₁ b₁ h) :
    x + y ∈ conePAnnulus p a₁ b₁ h := by
  constructor
  · intro t
    change 0 ≤ x t + y t
    exact add_nonneg (hx.1 t) (hy.1 t)
  · intro t ht
    change c_annulus p a₁ b₁ * ‖x + y‖ ≤
      x ⟨t, ⟨by linarith [h.1, ht.1], by linarith [h.2.2, ht.2]⟩⟩ +
      y ⟨t, ⟨by linarith [h.1, ht.1], by linarith [h.2.2, ht.2]⟩⟩
    calc
      _ ≤ c_annulus p a₁ b₁ * (‖x‖ + ‖y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le x y) (c_annulus_bounds p a₁ b₁ h).1.le
      _ = c_annulus p a₁ b₁ * ‖x‖ + c_annulus p a₁ b₁ * ‖y‖ := mul_add _ _ _
      _ ≤ _ := add_le_add (hx.2 t ht) (hy.2 t ht)

theorem conePAnnulus_smul_mem (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) {c : ℝ} {x : EAnnulus p}
    (hc : 0 ≤ c) (hx : x ∈ conePAnnulus p a₁ b₁ h) :
    c • x ∈ conePAnnulus p a₁ b₁ h := by
  constructor
  · intro t
    change 0 ≤ c * x t
    exact mul_nonneg hc (hx.1 t)
  · intro t ht
    change c_annulus p a₁ b₁ * ‖c • x‖ ≤
      c * x ⟨t, ⟨by linarith [h.1, ht.1], by linarith [h.2.2, ht.2]⟩⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      _ = c * (c_annulus p a₁ b₁ * ‖x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hx.2 t ht) hc

theorem conePAnnulus_strict (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) {x : EAnnulus p}
    (hx : x ∈ conePAnnulus p a₁ b₁ h) (hnx : -x ∈ conePAnnulus p a₁ b₁ h) : x = 0 := by
  ext t
  have hneg : 0 ≤ -x t := by simpa using hnx.1 t
  change x t = 0
  exact le_antisymm (neg_nonneg.mp hneg) (hx.1 t)

theorem conePAnnulus_isClosed (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) :
    IsClosed (conePAnnulus p a₁ b₁ h) := by
  have heq : conePAnnulus p a₁ b₁ h =
      (⋂ t : Icc p.a p.b, {φ : EAnnulus p | 0 ≤ φ t}) ∩
      (⋂ t : ℝ, ⋂ ht : t ∈ Icc a₁ b₁,
        {φ : EAnnulus p | c_annulus p a₁ b₁ * ‖φ‖ ≤
          φ ⟨t, ⟨by linarith [h.1, ht.1], by linarith [h.2.2, ht.2]⟩⟩}) := by
    ext φ
    simp [conePAnnulus]
  rw [heq]
  refine (isClosed_iInter fun t => ?_).inter (isClosed_iInter fun t => ?_)
  · exact isClosed_le continuous_const (continuous_eval_const t)
  · refine isClosed_iInter fun ht => ?_
    exact isClosed_le (continuous_const.mul continuous_norm)
      (continuous_eval_const (⟨t, ⟨by linarith [h.1, ht.1],
        by linarith [h.2.2, ht.2]⟩⟩ : Icc p.a p.b))

/-- Cone (15) packaged for Theorem 2.1. -/
noncomputable def conePAnnulusCone
    (p : AnnulusParams)
    (a₁ b₁ : ℝ)
    (ha₁b₁ : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) :
    Cone (EAnnulus p) where
  carrier := conePAnnulus p a₁ b₁ ha₁b₁
  nonempty := conePAnnulus_nonempty p a₁ b₁ ha₁b₁
  isClosed := conePAnnulus_isClosed p a₁ b₁ ha₁b₁
  add_mem := conePAnnulus_add_mem p a₁ b₁ ha₁b₁
  smul_mem := conePAnnulus_smul_mem p a₁ b₁ ha₁b₁
  strict := conePAnnulus_strict p a₁ b₁ ha₁b₁

/-- Extension of a continuous function on `[a,b]` to `ℝ` by projection. -/
noncomputable def extendAnnulus
    (p : AnnulusParams) (φ : EAnnulus p) (s : ℝ) : ℝ :=
  φ (projIcc p.a p.b p.hab.2.le s)

/-- Radial denominator in (12) and (14). -/
noncomputable def denominatorAnnulus
    (p : AnnulusParams) (φ : EAnnulus p) : ℝ :=
  (∫ s in p.a..p.b,
      p.pn * s ^ (p.n - 1) * p.f (extendAnnulus p φ s)) ^ p.β

/-- Integral operator (14), pointwise. -/
noncomputable def operatorSAnnulus
    (p : AnnulusParams)
    (φ : EAnnulus p)
    (t : Icc p.a p.b) : ℝ :=
  p.M * ∫ s in p.a..p.b,
    G_annulus p t.1 s *
      ((p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ)

/-- The operator (14) is continuous as a function of `t`. -/
lemma extendAnnulus_continuous (p : AnnulusParams) (φ : EAnnulus p) :
    Continuous (extendAnnulus p φ) := φ.continuous.comp continuous_projIcc

theorem operatorSAnnulus_continuous (p : AnnulusParams) (φ : EAnnulus p) :
    Continuous (fun t : Icc p.a p.b => operatorSAnnulus p φ t) := by
  let F : Icc p.a p.b → ℝ → ℝ := fun t s =>
    G_annulus p t (projIcc p.a p.b p.hab.2.le s) *
      ((p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ)
  have hproj : Continuous (projIcc p.a p.b p.hab.2.le) := continuous_projIcc
  have hF : Continuous F.uncurry :=
    ((G_annulus_continuous p).comp
      (continuous_fst.prodMk (hproj.comp continuous_snd))).mul
      (((p.hf_cont.comp ((extendAnnulus_continuous p φ).comp continuous_snd)).rpow_const
        (fun _ => Or.inr p.hα.le)).div_const _)
  have heq (t : Icc p.a p.b) : operatorSAnnulus p φ t = p.M * ∫ s in p.a..p.b, F t s := by
    unfold operatorSAnnulus
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc p.a p.b := by simpa [uIcc_of_le p.hab.2.le] using hs
    simp [F, projIcc_of_mem p.hab.2.le hs']
  simp_rw [heq]
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF p.a p.b)

/-- Operator (14) as a self-map of `E=C([a,b],ℝ)`. -/
noncomputable def SAnnulus
    (p : AnnulusParams) (φ : EAnnulus p) : EAnnulus p :=
  ⟨fun t => operatorSAnnulus p φ t, operatorSAnnulus_continuous p φ⟩

/-- Radial ODE (12), with Dirichlet boundary values. -/
def IsClassicalRadialSolution
    (p : AnnulusParams) (φ : EAnnulus p) : Prop :=
  (∀ t : ℝ, t ∈ Ioo p.a p.b →
    - deriv (fun r => deriv (extendAnnulus p φ) r) t
      - (((p.n : ℝ) - 1) / t) * deriv (extendAnnulus p φ) t =
        p.M * (p.f (extendAnnulus p φ t) ^ p.α) / denominatorAnnulus p φ) ∧
  φ (leftPointAnnulus p) = 0 ∧
  φ (rightPointAnnulus p) = 0 ∧
  ContDiffOn ℝ 2 (extendAnnulus p φ) (Icc p.a p.b)

lemma radial_power_hasDerivAt {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (k : ℝ) :
    HasDerivAt (fun t : ℝ => (c/t)^k) (-k*(c/t)^k/t) t := by
  have hd : HasDerivAt (fun t : ℝ => c/t) (-c/t^2) t := by
    simpa using (hasDerivAt_const t c).fun_div (hasDerivAt_id t) ht.ne'
  convert hd.rpow_const (Or.inl (div_ne_zero hc.ne' ht.ne')) using 1
  rw [Real.rpow_sub (div_pos hc ht) k 1, Real.rpow_one]
  field_simp

lemma radial_power_hasSecondDerivAt {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (k : ℝ) :
    HasDerivAt (fun t : ℝ => k*(c/t)^k/t) (-k*(k+1)*(c/t)^k/t^2) t := by
  convert ((radial_power_hasDerivAt hc ht k).const_mul k).fun_div (hasDerivAt_id t) ht.ne' using 1
  · rfl
  · dsimp
    field_simp
    ring

lemma radial_coefficients_continuous (p : AnnulusParams) :
    Continuous (fun t : Icc p.a p.b => A_radial p t) ∧
    Continuous (fun t : Icc p.a p.b => B_radial p t) ∧
    Continuous (fun t : Icc p.a p.b => deriv (B_radial p) t - deriv (A_radial p) t) := by
  have ht (t : Icc p.a p.b) : (t : ℝ) ≠ 0 := (lt_of_lt_of_le p.hab.1 t.2.1).ne'
  have hA : Continuous (fun t : Icc p.a p.b => A_radial p t) :=
    (continuous_const.div continuous_subtype_val ht).rpow_const (fun _ => Or.inr (radial_exponent_pos p).le)
  have hB : Continuous (fun t : Icc p.a p.b => B_radial p t) :=
    (continuous_const.div continuous_subtype_val ht).rpow_const (fun _ => Or.inr (radial_exponent_pos p).le)
  refine ⟨hA, hB, ?_⟩
  have heq (t : Icc p.a p.b) : deriv (B_radial p) t - deriv (A_radial p) t =
      (-((p.n : ℝ)-2)*B_radial p t/t) - (-((p.n : ℝ)-2)*A_radial p t/t) := by
    rw [show B_radial p = (fun s => (p.b/s)^((p.n : ℝ)-2)) from rfl,
      show A_radial p = (fun s => (p.a/s)^((p.n : ℝ)-2)) from rfl,
      deriv_radial_power (lt_trans p.hab.1 p.hab.2) (lt_of_lt_of_le p.hab.1 t.2.1),
      deriv_radial_power p.hab.1 (lt_of_lt_of_le p.hab.1 t.2.1)]
  simp_rw [heq]
  exact ((continuous_const.mul hB).div continuous_subtype_val ht).sub
    ((continuous_const.mul hA).div continuous_subtype_val ht)

noncomputable def radialAuxA (p : AnnulusParams) (φ : EAnnulus p) (s : ℝ) : ℝ :=
  let x := projIcc p.a p.b p.hab.2.le s
  (1-A_radial p x) * ((p.f (extendAnnulus p φ s)^p.α) / denominatorAnnulus p φ) /
    (deriv (B_radial p) x - deriv (A_radial p) x)

noncomputable def radialAuxB (p : AnnulusParams) (φ : EAnnulus p) (s : ℝ) : ℝ :=
  let x := projIcc p.a p.b p.hab.2.le s
  (1-B_radial p x) * ((p.f (extendAnnulus p φ s)^p.α) / denominatorAnnulus p φ) /
    (deriv (B_radial p) x - deriv (A_radial p) x)

lemma radialAux_continuous (p : AnnulusParams) (φ : EAnnulus p) :
    Continuous (radialAuxA p φ) ∧ Continuous (radialAuxB p φ) := by
  have hp : Continuous (projIcc p.a p.b p.hab.2.le) := continuous_projIcc
  obtain ⟨hA, hB, hW⟩ := radial_coefficients_continuous p
  have hg : Continuous (fun s => (p.f (extendAnnulus p φ s)^p.α) / denominatorAnnulus p φ) :=
    ((p.hf_cont.comp (extendAnnulus_continuous p φ)).rpow_const (fun _ => Or.inr p.hα.le)).div_const _
  have hw (s : ℝ) : deriv (B_radial p) (projIcc p.a p.b p.hab.2.le s) -
      deriv (A_radial p) (projIcc p.a p.b p.hab.2.le s) ≠ 0 :=
    (radial_wronskian_neg p (lt_of_lt_of_le p.hab.1 (projIcc p.a p.b p.hab.2.le s).2.1)).ne
  exact ⟨((continuous_const.sub (hA.comp hp)).mul hg).div (hW.comp hp) hw,
    ((continuous_const.sub (hB.comp hp)).mul hg).div (hW.comp hp) hw⟩

noncomputable def greenPrimitiveAnnulus (p : AnnulusParams) (φ : EAnnulus p) (t : ℝ) : ℝ :=
  p.M * ((1-B_radial p t)*(∫ s in p.a..t, radialAuxA p φ s) +
    (1-A_radial p t)*(∫ s in t..p.b, radialAuxB p φ s))

noncomputable def greenPrimitiveAnnulusFirst (p : AnnulusParams) (φ : EAnnulus p) (t : ℝ) : ℝ :=
  let k := (p.n : ℝ)-2
  p.M * ((k*B_radial p t/t)*(∫ s in p.a..t, radialAuxA p φ s) +
    (k*A_radial p t/t)*(∫ s in t..p.b, radialAuxB p φ s))

noncomputable def greenPrimitiveAnnulusSecond (p : AnnulusParams) (φ : EAnnulus p) (t : ℝ) : ℝ :=
  -(((p.n : ℝ)-1)/t) * greenPrimitiveAnnulusFirst p φ t -
    p.M * ((p.f (extendAnnulus p φ t)^p.α) / denominatorAnnulus p φ)

lemma greenPrimitiveAnnulus_derivatives (p : AnnulusParams) (φ : EAnnulus p) :
    (∀ t ∈ Icc p.a p.b, HasDerivAt (greenPrimitiveAnnulus p φ) (greenPrimitiveAnnulusFirst p φ t) t) ∧
    (∀ t ∈ Icc p.a p.b, HasDerivAt (greenPrimitiveAnnulusFirst p φ) (greenPrimitiveAnnulusSecond p φ t) t) := by
  let k := (p.n : ℝ)-2
  obtain ⟨hAc, hBc⟩ := radialAux_continuous p φ
  have hI (t : ℝ) : HasDerivAt (fun t => ∫ s in p.a..t, radialAuxA p φ s) (radialAuxA p φ t) t :=
    intervalIntegral.integral_hasDerivAt_right (hAc.intervalIntegrable _ _)
      hAc.aestronglyMeasurable.stronglyMeasurableAtFilter hAc.continuousAt
  have hJ (t : ℝ) : HasDerivAt (fun t => ∫ s in t..p.b, radialAuxB p φ s) (-radialAuxB p φ t) t :=
    intervalIntegral.integral_hasDerivAt_left (hBc.intervalIntegrable _ _)
      hBc.aestronglyMeasurable.stronglyMeasurableAtFilter hBc.continuousAt
  have hUd (t : ℝ) (ht : t ∈ Icc p.a p.b) : HasDerivAt (fun t => 1-A_radial p t) (k*A_radial p t/t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).fun_sub
      (radial_power_hasDerivAt p.hab.1 (lt_of_lt_of_le p.hab.1 ht.1) k) using 1 <;> dsimp [A_radial] <;> ring
  have hVd (t : ℝ) (ht : t ∈ Icc p.a p.b) : HasDerivAt (fun t => 1-B_radial p t) (k*B_radial p t/t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).fun_sub
      (radial_power_hasDerivAt (lt_trans p.hab.1 p.hab.2) (lt_of_lt_of_le p.hab.1 ht.1) k) using 1 <;> dsimp [B_radial] <;> ring
  constructor
  · intro t ht
    change HasDerivAt (fun t => p.M*((1-B_radial p t)*(∫ s in p.a..t, radialAuxA p φ s) +
      (1-A_radial p t)*(∫ s in t..p.b, radialAuxB p φ s))) _ t
    convert (((hVd t ht).fun_mul (hI t)).fun_add ((hUd t ht).fun_mul (hJ t))).const_mul p.M using 1
    dsimp [greenPrimitiveAnnulusFirst, radialAuxA, radialAuxB]
    rw [projIcc_of_mem p.hab.2.le ht]
    dsimp [k]
    ring
  · intro t ht
    have htpos := lt_of_lt_of_le p.hab.1 ht.1
    have hW : deriv (B_radial p) t - deriv (A_radial p) t ≠ 0 := (radial_wronskian_neg p htpos).ne
    have hU₁ := radial_power_hasSecondDerivAt p.hab.1 htpos k
    have hV₁ := radial_power_hasSecondDerivAt (lt_trans p.hab.1 p.hab.2) htpos k
    change HasDerivAt (fun t => k*A_radial p t/t) (-k*(k+1)*A_radial p t/t^2) t at hU₁
    change HasDerivAt (fun t => k*B_radial p t/t) (-k*(k+1)*B_radial p t/t^2) t at hV₁
    change HasDerivAt (fun t => p.M*((k*B_radial p t/t)*(∫ s in p.a..t, radialAuxA p φ s) +
      (k*A_radial p t/t)*(∫ s in t..p.b, radialAuxB p φ s))) _ t
    convert ((hV₁.fun_mul (hI t)).fun_add (hU₁.fun_mul (hJ t))).const_mul p.M using 1
    dsimp [greenPrimitiveAnnulusSecond, greenPrimitiveAnnulusFirst, radialAuxA, radialAuxB]
    rw [projIcc_of_mem p.hab.2.le ht]
    have heqW : deriv (B_radial p) t - deriv (A_radial p) t =
        -k*B_radial p t/t - (-k*A_radial p t/t) := by
      rw [show B_radial p = (fun s => (p.b/s)^((p.n : ℝ)-2)) from rfl,
        show A_radial p = (fun s => (p.a/s)^((p.n : ℝ)-2)) from rfl,
        deriv_radial_power (lt_trans p.hab.1 p.hab.2) htpos, deriv_radial_power p.hab.1 htpos]
    have hcross : (k*B_radial p t/t)*(1-A_radial p t) -
        (k*A_radial p t/t)*(1-B_radial p t) = -(deriv (B_radial p) t - deriv (A_radial p) t) := by
      rw [heqW]
      ring
    have hArel : -k*(k+1)*A_radial p t/t^2 = -(((p.n : ℝ)-1)/t)*(k*A_radial p t/t) := by
      dsimp [k]; field_simp; ring
    have hBrel : -k*(k+1)*B_radial p t/t^2 = -(((p.n : ℝ)-1)/t)*(k*B_radial p t/t) := by
      dsimp [k]; field_simp; ring
    rw [hArel, hBrel]
    have hcancel :
        (k*B_radial p t/t)*((1-A_radial p t)*((p.f (extendAnnulus p φ t)^p.α) / denominatorAnnulus p φ) /
          (deriv (B_radial p) t - deriv (A_radial p) t)) +
        (k*A_radial p t/t)*(-((1-B_radial p t)*((p.f (extendAnnulus p φ t)^p.α) / denominatorAnnulus p φ) /
          (deriv (B_radial p) t - deriv (A_radial p) t))) =
        -((p.f (extendAnnulus p φ t)^p.α) / denominatorAnnulus p φ) := by
      calc
        _ = ((k*B_radial p t/t)*(1-A_radial p t) - (k*A_radial p t/t)*(1-B_radial p t)) *
          ((p.f (extendAnnulus p φ t)^p.α) / denominatorAnnulus p φ) /
          (deriv (B_radial p) t - deriv (A_radial p) t) := by ring
        _ = _ := by rw [hcross]; field_simp
    linear_combination -p.M * hcancel

lemma greenPrimitiveAnnulus_regular (p : AnnulusParams) (φ : EAnnulus p) :
    ContDiffOn ℝ 2 (greenPrimitiveAnnulus p φ) (Icc p.a p.b) := by
  obtain ⟨h₁, h₂⟩ := greenPrimitiveAnnulus_derivatives p φ
  apply contDiffOn_two_of_derivatives p.hab.2 _ _ _ h₁ h₂
  have hc₁ : ContinuousOn (greenPrimitiveAnnulusFirst p φ) (Icc p.a p.b) :=
    fun t ht => (h₂ t ht).continuousAt.continuousWithinAt
  have hq : ContinuousOn (fun t : ℝ => ((p.n : ℝ)-1)/t) (Icc p.a p.b) :=
    continuousOn_const.div continuousOn_id (fun t ht => (lt_of_lt_of_le p.hab.1 ht.1).ne')
  exact (hq.neg.mul hc₁).sub ((continuous_const.mul
    (((p.hf_cont.comp (extendAnnulus_continuous p φ)).rpow_const
      (fun _ => Or.inr p.hα.le)).div_const _)).continuousOn)

lemma greenPrimitiveAnnulus_equation (p : AnnulusParams) (φ : EAnnulus p)
    {t : ℝ} (ht : t ∈ Ioo p.a p.b) :
    -deriv (deriv (greenPrimitiveAnnulus p φ)) t -
      (((p.n : ℝ)-1)/t) * deriv (greenPrimitiveAnnulus p φ) t =
      p.M * (p.f (extendAnnulus p φ t)^p.α) / denominatorAnnulus p φ := by
  obtain ⟨h₁, h₂⟩ := greenPrimitiveAnnulus_derivatives p φ
  have hev : deriv (greenPrimitiveAnnulus p φ) =ᶠ[𝓝 t] greenPrimitiveAnnulusFirst p φ := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact (h₁ s hs).deriv
  rw [hev.deriv_eq, (h₂ t (Ioo_subset_Icc_self ht)).deriv, (h₁ t (Ioo_subset_Icc_self ht)).deriv]
  dsimp [greenPrimitiveAnnulusSecond]
  ring

lemma greenPrimitiveAnnulus_boundary (p : AnnulusParams) (φ : EAnnulus p) :
    greenPrimitiveAnnulus p φ p.a = 0 ∧ greenPrimitiveAnnulus p φ p.b = 0 := by
  constructor
  · simp [greenPrimitiveAnnulus, A_radial, p.hab.1.ne']
  · simp [greenPrimitiveAnnulus, B_radial, (lt_trans p.hab.1 p.hab.2).ne']

lemma greenPrimitiveAnnulus_eq (p : AnnulusParams) (φ : EAnnulus p) (t : Icc p.a p.b) :
    SAnnulus p φ t = greenPrimitiveAnnulus p φ t := by
  let g := fun s => (p.f (extendAnnulus p φ s)^p.α) / denominatorAnnulus p φ
  have hg : Continuous g := ((p.hf_cont.comp (extendAnnulus_continuous p φ)).rpow_const
    (fun _ => Or.inr p.hα.le)).div_const _
  have hp : Continuous (projIcc p.a p.b p.hab.2.le) := continuous_projIcc
  have hk : ContinuousOn (fun s : ℝ => G_annulus p t s * g s) (Icc p.a p.b) := by
    apply ((((G_annulus_continuous p).comp ((continuous_const (y := t)).prodMk hp)).mul hg).continuousOn).congr
    intro s hs
    simp [projIcc_of_mem p.hab.2.le hs]
  have hi₁ : IntervalIntegrable (fun s => G_annulus p t s * g s) MeasureTheory.volume p.a t :=
    (hk.mono (Icc_subset_Icc le_rfl t.2.2)).intervalIntegrable_of_Icc t.2.1
  have hi₂ : IntervalIntegrable (fun s => G_annulus p t s * g s) MeasureTheory.volume t p.b :=
    (hk.mono (Icc_subset_Icc t.2.1 le_rfl)).intervalIntegrable_of_Icc t.2.2
  change p.M * (∫ s in p.a..p.b, G_annulus p t s * g s) =
    p.M * ((1-B_radial p t)*(∫ s in p.a..t, radialAuxA p φ s) +
      (1-A_radial p t)*(∫ s in (t : ℝ)..p.b, radialAuxB p φ s))
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
  congr 2
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc p.a t := by simpa [uIcc_of_le t.2.1] using hs
    have hs'' : s ∈ Icc p.a p.b := ⟨hs'.1, hs'.2.trans t.2.2⟩
    change G_annulus p t s * g s = (1-B_radial p t)*radialAuxA p φ s
    rw [G_annulus_eq, min_eq_right hs'.2, max_eq_left hs'.2]
    simp only [radialAuxA, projIcc_of_mem p.hab.2.le hs'']
    dsimp [g]
    ring
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (t : ℝ) p.b := by simpa [uIcc_of_le t.2.2] using hs
    have hs'' : s ∈ Icc p.a p.b := ⟨t.2.1.trans hs'.1, hs'.2⟩
    change G_annulus p t s * g s = (1-A_radial p t)*radialAuxB p φ s
    rw [G_annulus_eq, min_eq_left hs'.1, max_eq_right hs'.1]
    simp only [radialAuxB, projIcc_of_mem p.hab.2.le hs'']
    dsimp [g]
    ring

/-- Uniqueness of the homogeneous radial Dirichlet equation, using Rolle's theorem. -/
lemma radial_dirichlet_unique {a b q : ℝ} (ha : 0 < a) (hab : a < b)
    (f : ℝ → ℝ) (hc : ContDiffOn ℝ 2 f (Icc a b))
    (hode : ∀ t ∈ Ioo a b, -deriv (deriv f) t - (q/t)*deriv f t = 0)
    (hfa : f a = 0) (hfb : f b = 0) : ∀ t ∈ Icc a b, f t = 0 := by
  have hcd : ContDiffOn ℝ 1 (deriv f) (Ioo a b) :=
    (hc.mono Ioo_subset_Icc_self).deriv_of_isOpen isOpen_Ioo (by norm_num)
  let D := fun t => t^q * deriv f t
  have hD : ∀ t ∈ Ioo a b, HasDerivAt D 0 t := by
    intro t ht
    have htpos := lt_trans ha ht.1
    have hp : HasDerivAt (fun t : ℝ => t^q) (q*t^(q-1)) t :=
      by simpa only [id_eq, one_mul] using (hasDerivAt_id t).rpow_const (p := q) (Or.inl htpos.ne')
    have hd := (hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds ht)
    convert hp.fun_mul hd.hasDerivAt using 1
    rw [Real.rpow_sub htpos q 1, Real.rpow_one]
    have hh := hode t ht
    linear_combination (t^q)*hh
  obtain ⟨c, hc', hcz⟩ := exists_deriv_eq_zero hab hc.continuousOn (hfa.trans hfb.symm)
  have hDc : D c = 0 := by simp [D, hcz]
  have hDconst : ∀ t ∈ Ioo a b, D t = D c := fun t ht =>
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs => (hD s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hD s hs).deriv) ht hc'
  have hdz : ∀ t ∈ Ioo a b, deriv f t = 0 := by
    intro t ht
    exact (mul_eq_zero.mp ((hDconst t ht).trans hDc)).resolve_left
      (Real.rpow_pos_of_pos (lt_trans ha ht.1) q).ne'
  have hfconst := constant_on_interval_of_deriv_zero hab f hc.continuousOn
    ((hc.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self) hdz
  exact fun t ht => (hfconst t ht).trans hfa

/-- Equivalence between the radial BVP (12) and the integral equation (14). -/
theorem BVP12_iff_fixedPoint
    (p : AnnulusParams) (φ : EAnnulus p) (_hφ : ∀ t, 0 ≤ φ t) :
    IsClassicalRadialSolution p φ ↔ SAnnulus p φ = φ := by
  let u := greenPrimitiveAnnulus p φ
  have hu : ContDiffOn ℝ 2 u (Icc p.a p.b) := greenPrimitiveAnnulus_regular p φ
  obtain ⟨hua, hub⟩ := greenPrimitiveAnnulus_boundary p φ
  constructor
  · intro hclass
    let y := fun t => extendAnnulus p φ t-u t
    have hy : ContDiffOn ℝ 2 y (Icc p.a p.b) := hclass.2.2.2.sub hu
    have hyode : ∀ t ∈ Ioo p.a p.b, -deriv (deriv y) t -
        (((p.n : ℝ)-1)/t)*deriv y t = 0 := by
      intro t ht
      have hdf := (hclass.2.2.2.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds ht.1 ht.2)
      have hdu := (hu.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds ht.1 ht.2)
      rw [second_deriv_sub_on_interval _ _ hclass.2.2.2 hu ht, deriv_fun_sub hdf hdu]
      have hφeq := hclass.1 t ht
      have hueq := greenPrimitiveAnnulus_equation p φ ht
      change -deriv (deriv (extendAnnulus p φ)) t - _ = _ at hφeq
      linear_combination hφeq - hueq
    have hya : y p.a = 0 := by
      have hfa : extendAnnulus p φ p.a = 0 := by
        rw [extendAnnulus, projIcc_of_mem p.hab.2.le (show p.a ∈ Icc p.a p.b from ⟨le_rfl, p.hab.2.le⟩)]
        exact hclass.2.1
      simp only [y, hfa, hua, sub_self, u]
    have hyb : y p.b = 0 := by
      have hfb : extendAnnulus p φ p.b = 0 := by
        rw [extendAnnulus, projIcc_of_mem p.hab.2.le (show p.b ∈ Icc p.a p.b from ⟨p.hab.2.le, le_rfl⟩)]
        exact hclass.2.2.1
      simp only [y, hfb, hub, sub_self, u]
    have hz := radial_dirichlet_unique p.hab.1 p.hab.2 y hy hyode hya hyb
    ext t
    have hh : extendAnnulus p φ t = u t := sub_eq_zero.mp (hz t t.2)
    rw [greenPrimitiveAnnulus_eq]
    exact hh.symm.trans (by simp [extendAnnulus, projIcc_of_mem p.hab.2.le t.2])
  · intro hfix
    have heq : EqOn (extendAnnulus p φ) u (Icc p.a p.b) := by
      intro t ht
      rw [extendAnnulus, projIcc_of_mem p.hab.2.le ht]
      rw [← hfix]
      exact greenPrimitiveAnnulus_eq p φ ⟨t, ht⟩
    refine ⟨?_, ?_, ?_, hu.congr heq⟩
    · intro t ht
      have hev : extendAnnulus p φ =ᶠ[𝓝 t] u := by
        filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
        exact heq hs
      rw [hev.deriv.deriv_eq, hev.deriv_eq]
      exact greenPrimitiveAnnulus_equation p φ ht
    · have hh := heq (show p.a ∈ Icc p.a p.b from ⟨le_rfl, p.hab.2.le⟩)
      rw [extendAnnulus, projIcc_of_mem p.hab.2.le (show p.a ∈ Icc p.a p.b from ⟨le_rfl, p.hab.2.le⟩)] at hh
      exact hh.trans hua
    · have hh := heq (show p.b ∈ Icc p.a p.b from ⟨p.hab.2.le, le_rfl⟩)
      rw [extendAnnulus, projIcc_of_mem p.hab.2.le (show p.b ∈ Icc p.a p.b from ⟨p.hab.2.le, le_rfl⟩)] at hh
      exact hh.trans hub

lemma radial_power_antitone {c k x y : ℝ} (hc : 0 < c) (hk : 0 ≤ k)
    (hx : 0 < x) (hxy : x ≤ y) : (c / y) ^ k ≤ (c / x) ^ k :=
  Real.rpow_le_rpow (div_nonneg hc.le (le_trans hx.le hxy))
    (div_le_div_of_nonneg_left hc.le hx hxy) hk

/-- Uniform Harnack bound for the radial Green kernel. -/
lemma G_annulus_harnack (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) {t s r : ℝ}
    (ht : t ∈ Icc a₁ b₁) (hs : s ∈ Icc p.a p.b) (hr : r ∈ Icc p.a p.b) :
    c_annulus p a₁ b₁ * G_annulus p r s ≤ G_annulus p t s := by
  let U : ℝ → ℝ := fun x => 1 - A_radial p x
  let V : ℝ → ℝ := fun x => B_radial p x - 1
  let D : ℝ := max (V p.a) (U p.b)
  let c : ℝ := c_annulus p a₁ b₁
  have hc : 0 < c := (c_annulus_bounds p a₁ b₁ h).1
  have ht' : t ∈ Icc p.a p.b := ⟨le_trans h.1.le ht.1, le_trans ht.2 h.2.2.le⟩
  have hu (x : ℝ) (hx : x ∈ Icc p.a p.b) : 0 ≤ U x := sub_nonneg.mpr (A_radial_le_one p hx)
  have hv (x : ℝ) (hx : x ∈ Icc p.a p.b) : 0 ≤ V x := sub_nonneg.mpr (one_le_B_radial p hx)
  have hU {x y : ℝ} (hx : p.a ≤ x) (hxy : x ≤ y) : U x ≤ U y := by
    apply sub_le_sub_left
    exact radial_power_antitone p.hab.1 (radial_exponent_pos p).le
      (lt_of_lt_of_le p.hab.1 hx) hxy
  have hV {x y : ℝ} (hx : p.a ≤ x) (hxy : x ≤ y) : V y ≤ V x := by
    apply sub_le_sub_right
    exact radial_power_antitone (lt_trans p.hab.1 p.hab.2) (radial_exponent_pos p).le
      (lt_of_lt_of_le p.hab.1 hx) hxy
  have hD : 0 < D := by
    have hVa : 0 < V p.a := sub_pos.mpr
      (Real.one_lt_rpow ((one_lt_div p.hab.1).2 p.hab.2) (radial_exponent_pos p))
    exact lt_of_lt_of_le hVa (le_max_left _ _)
  have hcD : c * D = min (V b₁) (U a₁) := by
    change (min (V b₁) (U a₁) / D) * D = _
    exact div_mul_cancel₀ _ hD.ne'
  have hcu (x : ℝ) (hx : x ∈ Icc p.a p.b) : c * U x ≤ U t := by
    calc
      _ ≤ c * D := mul_le_mul_of_nonneg_left
        ((hU hx.1 hx.2).trans (le_max_right _ _)) hc.le
      _ = min (V b₁) (U a₁) := hcD
      _ ≤ U a₁ := min_le_right _ _
      _ ≤ U t := hU h.1.le ht.1
  have hcv (x : ℝ) (hx : x ∈ Icc p.a p.b) : c * V x ≤ V t := by
    calc
      _ ≤ c * D := mul_le_mul_of_nonneg_left
        ((hV le_rfl hx.1).trans (le_max_left _ _)) hc.le
      _ = min (V b₁) (U a₁) := hcD
      _ ≤ V b₁ := min_le_left _ _
      _ ≤ V t := hV ht'.1 ht.2
  let W : ℝ := deriv (B_radial p) s - deriv (A_radial p) s
  have hW : 0 < -W := neg_pos.mpr (radial_wronskian_neg p (lt_of_lt_of_le p.hab.1 hs.1))
  have hform (x : ℝ) : G_annulus p x s =
      (if s ≤ x then V x * U s else U x * V s) / (-W) := by
    unfold G_annulus
    dsimp [W, U, V]
    split_ifs <;> simp only [div_neg]
    · ring
    · ring
  rw [hform r, hform t, ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right hW).2
  by_cases hst : s ≤ t <;> by_cases hsr : s ≤ r
  · rw [ite_eq_left hst, ite_eq_left hsr]
    calc
      _ = (c * V r) * U s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcv r hr) (hu s hs)
  · rw [ite_eq_left hst, ite_eq_right hsr]
    calc
      _ = (c * V s) * U r := by ring
      _ ≤ V t * U r := mul_le_mul_of_nonneg_right (hcv s hs) (hu r hr)
      _ ≤ V t * U s := mul_le_mul_of_nonneg_left (hU hr.1 (le_of_not_ge hsr)) (hv t ht')
  · rw [ite_eq_right hst, ite_eq_left hsr]
    calc
      _ = (c * U s) * V r := by ring
      _ ≤ U t * V r := mul_le_mul_of_nonneg_right (hcu s hs) (hv r hr)
      _ ≤ U t * V s := mul_le_mul_of_nonneg_left (hV hs.1 hsr) (hu t ht')
  · rw [ite_eq_right hst, ite_eq_right hsr]
    calc
      _ = (c * U r) * V s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcu r hr) (hv s hs)

/-- Invariance of the radial cone, proved from the kernel inequality. -/
theorem SAnnulus_maps_cone (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) {φ : EAnnulus p}
    (hφ : φ ∈ conePAnnulus p a₁ b₁ h) :
    SAnnulus p φ ∈ conePAnnulus p a₁ b₁ h := by
  let c : ℝ := c_annulus p a₁ b₁
  have hc : 0 < c := (c_annulus_bounds p a₁ b₁ h).1
  let g : ℝ → ℝ := fun s => (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ
  have hgcont : Continuous g :=
    ((p.hf_cont.comp (extendAnnulus_continuous p φ)).rpow_const
      (fun _ => Or.inr p.hα.le)).div_const _
  have hden : 0 ≤ denominatorAnnulus p φ := by
    unfold denominatorAnnulus
    apply Real.rpow_nonneg
    apply intervalIntegral.integral_nonneg p.hab.2.le
    intro s hs
    apply mul_nonneg
    · exact mul_nonneg p.hpn.le (pow_nonneg (le_trans p.hab.1.le hs.1) _)
    · exact (p.hf_pos _ (hφ.1 _)).le
  have hg (s : ℝ) : 0 ≤ g s :=
    div_nonneg (Real.rpow_pos_of_pos (p.hf_pos _ (hφ.1 _)) _).le hden
  have hint (t : Icc p.a p.b) :
      IntervalIntegrable (fun s => G_annulus p t s * g s) MeasureTheory.volume p.a p.b := by
    have hproj : Continuous (projIcc p.a p.b p.hab.2.le) := continuous_projIcc
    have hcont : Continuous (fun s : ℝ => G_annulus p t (projIcc p.a p.b p.hab.2.le s) * g s) :=
      ((G_annulus_continuous p).comp (continuous_const.prodMk hproj)).mul hgcont
    apply (hcont.intervalIntegrable p.a p.b).congr
    intro s hs
    have hs'' : s ∈ Ioc p.a p.b := by simpa [uIoc_of_le p.hab.2.le] using hs
    have hs' : s ∈ Icc p.a p.b := ⟨hs''.1.le, hs''.2⟩
    simp [projIcc_of_mem p.hab.2.le hs']
  have hnn (t : Icc p.a p.b) : 0 ≤ SAnnulus p φ t := by
    change 0 ≤ p.M * ∫ s in p.a..p.b, G_annulus p t s * g s
    exact mul_nonneg p.hM.le (intervalIntegral.integral_nonneg p.hab.2.le
      (fun s hs => mul_nonneg (G_annulus_nonneg p t.2 hs) (hg s)))
  constructor
  · exact hnn
  · intro t ht
    let tt : Icc p.a p.b := ⟨t, ⟨by linarith [h.1, ht.1], by linarith [h.2.2, ht.2]⟩⟩
    have hlow (r : Icc p.a p.b) : c * SAnnulus p φ r ≤ SAnnulus p φ tt := by
      change c * (p.M * (∫ s in p.a..p.b, G_annulus p r s * g s)) ≤
        p.M * ∫ s in p.a..p.b, G_annulus p t s * g s
      rw [← mul_assoc, mul_comm c p.M, mul_assoc, ← intervalIntegral.integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ p.hM.le
      apply intervalIntegral.integral_mono_on p.hab.2.le
        ((hint r).const_mul c) (hint tt)
      intro s hs
      change c * (G_annulus p r s * g s) ≤ G_annulus p t s * g s
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (G_annulus_harnack p a₁ b₁ h ht hs r.2) (hg s)
    have hnorm : ‖c • SAnnulus p φ‖ ≤ SAnnulus p φ tt := by
      apply (ContinuousMap.norm_le _ (hnn tt)).2
      intro r
      change ‖c * SAnnulus p φ r‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le (hnn r))]
      exact hlow r
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hc] using hnorm

/-- The radial weight has strictly positive integral on a nondegenerate interval. -/
lemma annulus_weight_pos (p : AnnulusParams) {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    0 < ∫ s in c..d, p.pn * s ^ (p.n - 1) := by
  apply intervalIntegral.integral_pos hcd
    (continuous_const.mul (continuous_id.pow _)).continuousOn
  · intro s hs
    exact mul_nonneg p.hpn.le (pow_nonneg (lt_trans hc hs.1).le _)
  · exact ⟨c, ⟨le_rfl, hcd.le⟩, mul_pos p.hpn (pow_pos hc _)⟩

lemma denominatorAnnulus_lower (p : AnnulusParams) (φ : EAnnulus p)
    (hφ : ∀ t, 0 ≤ φ t) :
    ((∫ s in p.a..p.b, p.pn * s ^ (p.n - 1)) * p.f 0) ^ p.β ≤
      denominatorAnnulus p φ := by
  have hw : Continuous (fun s : ℝ => p.pn * s ^ (p.n - 1)) :=
    continuous_const.mul (continuous_id.pow _)
  have hi : (∫ s in p.a..p.b, p.pn * s ^ (p.n - 1)) * p.f 0 ≤
      ∫ s in p.a..p.b, p.pn * s ^ (p.n - 1) * p.f (extendAnnulus p φ s) := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_mono_on p.hab.2.le
      ((hw.mul continuous_const).intervalIntegrable _ _)
      ((hw.mul (p.hf_cont.comp (extendAnnulus_continuous p φ))).intervalIntegrable _ _)
    intro s hs
    exact mul_le_mul_of_nonneg_left
      (p.hf_mono (show (0 : ℝ) ∈ Ici (0 : ℝ) from by simp) (hφ _) (hφ _))
      (mul_nonneg p.hpn.le (pow_nonneg (lt_of_lt_of_le p.hab.1 hs.1).le _))
  exact Real.rpow_le_rpow
    (mul_pos (annulus_weight_pos p p.hab.1 p.hab.2) (p.hf_pos 0 le_rfl)).le hi p.hβ.le

lemma denominatorAnnulus_pos (p : AnnulusParams) (φ : EAnnulus p)
    (hφ : ∀ t, 0 ≤ φ t) : 0 < denominatorAnnulus p φ :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos
    (mul_pos (annulus_weight_pos p p.hab.1 p.hab.2) (p.hf_pos 0 le_rfl)) _)
    (denominatorAnnulus_lower p φ hφ)

/-- Continuity of the radial operator in its input. -/
theorem SAnnulus_continuousOn (p : AnnulusParams) :
    ContinuousOn (SAnnulus p) {φ | ∀ t, 0 ≤ φ t} := by
  let D := {φ : EAnnulus p | ∀ t, 0 ≤ φ t}
  have hp : Continuous (projIcc p.a p.b p.hab.2.le) := continuous_projIcc
  have he : Continuous (fun q : D × ℝ => extendAnnulus p q.1.1 q.2) :=
    continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (hp.comp continuous_snd))
  have hi : Continuous (fun φ : D => ∫ s in p.a..p.b,
      p.pn * s ^ (p.n - 1) * p.f (extendAnnulus p φ.1 s)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ p.a p.b
    exact (continuous_const.mul (continuous_snd.pow _)).mul (p.hf_cont.comp he)
  have hd : Continuous (fun φ : D => denominatorAnnulus p φ.1) :=
    hi.rpow_const (fun _ => Or.inr p.hβ.le)
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  let F : (D × Icc p.a p.b) → ℝ → ℝ := fun q s =>
    G_annulus p q.2 (projIcc p.a p.b p.hab.2.le s) *
      ((p.f (extendAnnulus p q.1.1 s) ^ p.α) / denominatorAnnulus p q.1.1)
  have hF : Continuous F.uncurry := by
    have he' : Continuous (fun q : (D × Icc p.a p.b) × ℝ =>
        extendAnnulus p q.1.1.1 q.2) :=
      he.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact ((G_annulus_continuous p).comp
      ((continuous_snd.comp continuous_fst).prodMk (hp.comp continuous_snd))).mul
      (((p.hf_cont.comp he').rpow_const (fun _ => Or.inr p.hα.le)).div
        (hd.comp (continuous_fst.comp continuous_fst))
        (fun q => ne_of_gt (denominatorAnnulus_pos p q.1.1.1 q.1.1.2)))
  have heq (q : D × Icc p.a p.b) :
      SAnnulus p q.1.1 q.2 = p.M * ∫ s in p.a..p.b, F q s := by
    change p.M * _ = p.M * _
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    simp [F, projIcc_of_mem p.hab.2.le
      (show s ∈ Icc p.a p.b from by simpa [uIcc_of_le p.hab.2.le] using hs)]
  change Continuous (fun q : D × Icc p.a p.b => SAnnulus p q.1.1 q.2)
  simp_rw [heq]
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF p.a p.b)

/-- Complete continuity of the annulus operator, used in Theorem 3.1. -/
theorem SAnnulus_completelyContinuous
    (p : AnnulusParams) :
    CompletelyContinuousOn (SAnnulus p) {φ | ∀ t, 0 ≤ φ t} := by
  refine ⟨SAnnulus_continuousOn p, ?_⟩
  intro A hA hbA
  obtain ⟨U, hU⟩ := hbA.exists_pos_norm_le
  let d := ((∫ s in p.a..p.b, p.pn * s ^ (p.n - 1)) * p.f 0) ^ p.β
  have hd : 0 < d := Real.rpow_pos_of_pos
    (mul_pos (annulus_weight_pos p p.hab.1 p.hab.2) (p.hf_pos 0 le_rfl)) _
  let L := p.f U ^ p.α / d
  have hL : 0 ≤ L := div_nonneg (Real.rpow_nonneg (p.hf_pos U hU.1.le).le _) hd.le
  let k : Icc p.a p.b → C(Icc p.a p.b, ℝ) := fun t =>
    ⟨fun s => G_annulus p t s, (G_annulus_continuous p).comp
      (continuous_const.prodMk continuous_id)⟩
  have hk : Continuous k := ContinuousMap.continuous_of_continuous_uncurry _
    (G_annulus_continuous p)
  obtain ⟨C, hC⟩ := (isCompact_range hk).isBounded.exists_pos_norm_le
  let K := p.M * L * (p.b-p.a)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg p.hM.le hL) (sub_nonneg.mpr p.hab.2.le)
  have hb (φ : EAnnulus p) (hφ : φ ∈ A) (s : ℝ) :
      ‖(p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ‖ ≤ L := by
    have hf0 := p.hf_pos (extendAnnulus p φ s) (hA hφ (projIcc p.a p.b p.hab.2.le s))
    have hfs : p.f (extendAnnulus p φ s) ≤ p.f U := by
      apply p.hf_mono (hA hφ _) hU.1.le
      exact (le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm φ _).trans (hU.2 φ hφ))
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (Real.rpow_nonneg hf0.le _) (denominatorAnnulus_pos p φ (hA hφ)).le)]
    exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hf0.le _)
      hd (denominatorAnnulus_lower p φ (hA hφ))).trans
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow hf0.le hfs p.hα.le) hd.le)
  have estimates (φ : EAnnulus p) (hφ : φ ∈ A) (t u : Icc p.a p.b) :
      ‖SAnnulus p φ t‖ ≤ K * ‖k t‖ ∧
      dist (SAnnulus p φ t) (SAnnulus p φ u) ≤ K * dist (k t) (k u) := by
    let g := fun s => (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ
    have hg : Continuous g := ((p.hf_cont.comp (extendAnnulus_continuous p φ)).rpow_const
      (fun _ => Or.inr p.hα.le)).div_const _
    have hh := kernel_integral_bounds p.hab.2.le p.hM.le hL g hg
      (fun s _ => hb φ hφ s) (k t) (k u)
    have heq (r : Icc p.a p.b) :
        (∫ s in p.a..p.b, k r (projIcc p.a p.b p.hab.2.le s) * g s) =
        ∫ s in p.a..p.b, G_annulus p r s * g s := by
      apply intervalIntegral.integral_congr
      intro s hs
      simp [k, projIcc_of_mem p.hab.2.le
        (show s ∈ Icc p.a p.b from by simpa [uIcc_of_le p.hab.2.le] using hs)]
    simpa only [heq, SAnnulus, operatorSAnnulus, ContinuousMap.coe_mk, g, K] using hh
  apply compact_closure_of_kernel_bound (SAnnulus p '' A) k hk (K * C) K hK
  · rintro _ ⟨φ, hφ, rfl⟩
    apply (ContinuousMap.norm_le _ (mul_nonneg hK hC.1.le)).2
    intro t
    exact (estimates φ hφ t t).1.trans
      (mul_le_mul_of_nonneg_left (hC.2 _ (Set.mem_range_self t)) hK)
  · rintro _ ⟨φ, hφ, rfl⟩ t u
    exact (estimates φ hφ t u).2

/-- The supremum factor in the definition of `N` in Theorem 3.1. -/
noncomputable def annulusGreenSup (p : AnnulusParams) : ℝ :=
  sSup (Set.range (fun t : Icc p.a p.b =>
    ∫ s in p.a..p.b, G_annulus p t.1 s))

/-- Compression threshold for general β.

The printed Theorem 3.1 has the weight integral to the first power.
The estimate from the operator denominator gives power β; the two
formulas agree when β=1. Here we use that general-β correction. -/
noncomputable def N_annulus
    (p : AnnulusParams) (a₁ b₁ : ℝ) : ℝ :=
  ((∫ s in a₁..b₁, p.pn * s ^ (p.n - 1)) ^ p.β) *
    (p.M * annulusGreenSup p)⁻¹

/-- Growth assumption (a) in Theorem 3.1. -/
def ConditionAnnulus
    (p : AnnulusParams) (a₁ b₁ : ℝ) : Prop :=
  Filter.limsup
      (fun u =>
        ((((p.f u ^ p.α) /
          (u * (p.f (c_annulus p a₁ b₁ * u) ^ p.β))) : ℝ) : EReal))
      atTop
    < (N_annulus p a₁ b₁ : EReal)

/-- Fixed-point formulation of a positive radial solution of (11)/(12). -/
def IsPositiveRadialSolution
    (p : AnnulusParams) (φ : EAnnulus p) : Prop :=
  (∀ t : Icc p.a p.b, t.1 ∈ Ioo p.a p.b → 0 < φ t) ∧
  φ (leftPointAnnulus p) = 0 ∧
  φ (rightPointAnnulus p) = 0 ∧
  SAnnulus p φ = φ

/-- Dirichlet boundary values of the annulus operator. -/
lemma G_annulus_at_left (p : AnnulusParams) {s : ℝ} (hs : s ∈ Icc p.a p.b) :
    G_annulus p p.a s = 0 := by
  by_cases hsa : s ≤ p.a
  · have heq : s = p.a := le_antisymm hsa hs.1
    subst s
    simp [G_annulus, A_radial, p.hab.1.ne']
  · simp [G_annulus, hsa, A_radial, p.hab.1.ne']

lemma G_annulus_at_right (p : AnnulusParams) {s : ℝ} (hs : s ∈ Icc p.a p.b) :
    G_annulus p p.b s = 0 := by
  have hb : p.b ≠ 0 := (lt_trans p.hab.1 p.hab.2).ne'
  simp [G_annulus, hs.2, B_radial, hb]

theorem SAnnulus_boundary (p : AnnulusParams) (φ : EAnnulus p) :
    SAnnulus p φ (leftPointAnnulus p) = 0 ∧
    SAnnulus p φ (rightPointAnnulus p) = 0 := by
  constructor
  · change p.M * (∫ s in p.a..p.b, G_annulus p p.a s *
      ((p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ)) = 0
    have h : (∫ s in p.a..p.b, G_annulus p p.a s *
        ((p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ)) =
        ∫ _s in p.a..p.b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc p.a p.b := by simpa [uIcc_of_le p.hab.2.le] using hs
      simp [G_annulus_at_left p hs']
    rw [h]
    simp
  · change p.M * (∫ s in p.a..p.b, G_annulus p p.b s *
      ((p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ)) = 0
    have h : (∫ s in p.a..p.b, G_annulus p p.b s *
        ((p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ)) =
        ∫ _s in p.a..p.b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc p.a p.b := by simpa [uIcc_of_le p.hab.2.le] using hs
      simp [G_annulus_at_right p hs']
    rw [h]
    simp

lemma G_annulus_pos (p : AnnulusParams) {t s : ℝ}
    (ht : t ∈ Ioo p.a p.b) (hs : s ∈ Ioo p.a p.b) : 0 < G_annulus p t s := by
  have hmin : p.a < min t s := lt_min ht.1 hs.1
  have hmax : max t s < p.b := max_lt ht.2 hs.2
  have hm : 0 < min t s := lt_trans p.hab.1 hmin
  have hmx : 0 < max t s := lt_of_lt_of_le (lt_trans p.hab.1 ht.1) (le_max_left _ _)
  have hA : A_radial p (min t s) < 1 := Real.rpow_lt_one
    (div_nonneg p.hab.1.le hm.le) ((div_lt_one hm).2 hmin) (radial_exponent_pos p)
  have hB : 1 < B_radial p (max t s) := Real.one_lt_rpow
    ((one_lt_div hmx).2 hmax) (radial_exponent_pos p)
  rw [G_annulus_eq]
  exact div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (sub_neg.mpr hB) (sub_pos.mpr hA))
    (radial_wronskian_neg p (lt_trans p.hab.1 hs.1))

lemma annulus_kernel_intervalIntegrable (p : AnnulusParams) (t : Icc p.a p.b)
    (g : ℝ → ℝ) (hg : Continuous g) :
    IntervalIntegrable (fun s => G_annulus p t s * g s) MeasureTheory.volume p.a p.b := by
  have hp : Continuous (projIcc p.a p.b p.hab.2.le) := continuous_projIcc
  have hc : IntervalIntegrable (fun s => G_annulus p t (projIcc p.a p.b p.hab.2.le s) * g s) MeasureTheory.volume p.a p.b :=
    (((G_annulus_continuous p).comp ((continuous_const (y := t)).prodMk hp)).mul hg).intervalIntegrable p.a p.b
  apply hc.congr
  intro s hs
  have hs' : s ∈ Icc p.a p.b := Ioc_subset_Icc_self (by simpa [uIoc_of_le p.hab.2.le] using hs)
  simp [projIcc_of_mem p.hab.2.le hs']

lemma annulus_kernel_integral_continuous (p : AnnulusParams) :
    Continuous (fun t : Icc p.a p.b => ∫ s in p.a..p.b, G_annulus p t s) := by
  have hp : Continuous (projIcc p.a p.b p.hab.2.le) := continuous_projIcc
  have hc : Continuous (fun t : Icc p.a p.b => ∫ s in p.a..p.b, G_annulus p t (projIcc p.a p.b p.hab.2.le s)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ p.a p.b
    exact (G_annulus_continuous p).comp (continuous_fst.prodMk (hp.comp continuous_snd))
  have heq (t : Icc p.a p.b) :
      (∫ s in p.a..p.b, G_annulus p t (projIcc p.a p.b p.hab.2.le s)) =
      ∫ s in p.a..p.b, G_annulus p t s := by
    apply intervalIntegral.integral_congr
    intro s hs
    simp [projIcc_of_mem p.hab.2.le (show s ∈ Icc p.a p.b from by simpa [uIcc_of_le p.hab.2.le] using hs)]
  simpa only [heq] using hc

lemma annulus_kernel_integral_pos (p : AnnulusParams) (t : Icc p.a p.b)
    (ht : t.1 ∈ Ioo p.a p.b) : 0 < ∫ s in p.a..p.b, G_annulus p t s := by
  have hp : Continuous (projIcc p.a p.b p.hab.2.le) := continuous_projIcc
  have hc : ContinuousOn (fun s : ℝ => G_annulus p t s) (Icc p.a p.b) := by
    apply (((G_annulus_continuous p).comp ((continuous_const (y := t)).prodMk hp)).continuousOn).congr
    intro s hs
    simp [projIcc_of_mem p.hab.2.le hs]
  apply intervalIntegral.integral_pos p.hab.2 hc
    (fun s hs => G_annulus_nonneg p t.2 ⟨hs.1.le, hs.2⟩)
  exact ⟨t, t.2, G_annulus_pos p ht ht⟩

lemma annulusGreenSup_bound (p : AnnulusParams) (t : Icc p.a p.b) :
    (∫ s in p.a..p.b, G_annulus p t s) ≤ annulusGreenSup p := by
  exact le_csSup (isCompact_range (annulus_kernel_integral_continuous p)).bddAbove (Set.mem_range_self t)

lemma annulusGreenSup_pos (p : AnnulusParams) : 0 < annulusGreenSup p := by
  let t : Icc p.a p.b := ⟨(p.a+p.b)/2, by constructor <;> linarith [p.hab.2]⟩
  exact (annulus_kernel_integral_pos p t (by constructor <;> dsimp [t] <;> linarith [p.hab.2])).trans_le
    (annulusGreenSup_bound p t)

lemma SAnnulus_norm_bounds (p : AnnulusParams) (φ : EAnnulus p) (hφ : ∀ t, 0 ≤ φ t)
    (t₀ : Icc p.a p.b) {l u : ℝ} (_hl : 0 ≤ l) (hu : 0 ≤ u)
    (hg : ∀ s ∈ Icc p.a p.b,
      l ≤ (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ ∧
      (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ ≤ u) :
    p.M * l * (∫ s in p.a..p.b, G_annulus p t₀ s) ≤ ‖SAnnulus p φ‖ ∧
      ‖SAnnulus p φ‖ ≤ p.M * u * annulusGreenSup p := by
  let g := fun s => (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ
  have hc : Continuous g := ((p.hf_cont.comp (extendAnnulus_continuous p φ)).rpow_const
    (fun _ => Or.inr p.hα.le)).div_const _
  have hgc : ∀ s, 0 ≤ g s := fun s => div_nonneg
    (Real.rpow_nonneg (p.hf_pos _ (hφ _)).le _) (denominatorAnnulus_pos p φ hφ).le
  have hlo : p.M * l * (∫ s in p.a..p.b, G_annulus p t₀ s) ≤ SAnnulus p φ t₀ := by
    have hi : (∫ s in p.a..p.b, G_annulus p t₀ s * l) ≤ ∫ s in p.a..p.b, G_annulus p t₀ s * g s :=
      intervalIntegral.integral_mono_on p.hab.2.le
        (annulus_kernel_intervalIntegrable p t₀ _ continuous_const)
        (annulus_kernel_intervalIntegrable p t₀ g hc)
        (fun s hs => mul_le_mul_of_nonneg_left (hg s hs).1 (G_annulus_nonneg p t₀.2 hs))
    rw [intervalIntegral.integral_mul_const] at hi
    change _ ≤ p.M * ∫ s in p.a..p.b, G_annulus p t₀ s * g s
    nlinarith [mul_le_mul_of_nonneg_left hi p.hM.le]
  have hnn (t : Icc p.a p.b) : 0 ≤ SAnnulus p φ t := by
    change 0 ≤ p.M * ∫ s in p.a..p.b, G_annulus p t s * g s
    exact mul_nonneg p.hM.le (intervalIntegral.integral_nonneg p.hab.2.le
      (fun s hs => mul_nonneg (G_annulus_nonneg p t.2 hs) (hgc s)))
  refine ⟨hlo.trans ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
    (ContinuousMap.norm_coe_le_norm (SAnnulus p φ) t₀))), ?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg p.hM.le hu) (annulusGreenSup_pos p).le)).2
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]
  have hi : (∫ s in p.a..p.b, G_annulus p t s * g s) ≤ ∫ s in p.a..p.b, G_annulus p t s * u :=
    intervalIntegral.integral_mono_on p.hab.2.le
      (annulus_kernel_intervalIntegrable p t g hc)
      (annulus_kernel_intervalIntegrable p t _ continuous_const)
      (fun s hs => mul_le_mul_of_nonneg_left (hg s hs).2 (G_annulus_nonneg p t.2 hs))
  rw [intervalIntegral.integral_mul_const] at hi
  change p.M * (∫ s in p.a..p.b, G_annulus p t s * g s) ≤ _
  calc
    _ ≤ p.M * ((∫ s in p.a..p.b, G_annulus p t s) * u) := mul_le_mul_of_nonneg_left hi p.hM.le
    _ = (p.M*u)*(∫ s in p.a..p.b, G_annulus p t s) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (annulusGreenSup_bound p t) (mul_nonneg p.hM.le hu)

lemma SAnnulus_strictlyPositive (p : AnnulusParams) (φ : EAnnulus p) (hφ : ∀ t, 0 ≤ φ t)
    (t : Icc p.a p.b) (ht : t.1 ∈ Ioo p.a p.b) : 0 < SAnnulus p φ t := by
  let g := fun s => (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ
  have hc : Continuous g := ((p.hf_cont.comp (extendAnnulus_continuous p φ)).rpow_const
    (fun _ => Or.inr p.hα.le)).div_const _
  have hp : Continuous (projIcc p.a p.b p.hab.2.le) := continuous_projIcc
  have hcont : ContinuousOn (fun s : ℝ => G_annulus p t s * g s) (Icc p.a p.b) := by
    apply ((((G_annulus_continuous p).comp ((continuous_const (y := t)).prodMk hp)).mul hc).continuousOn).congr
    intro s hs
    simp [projIcc_of_mem p.hab.2.le hs]
  change 0 < p.M * ∫ s in p.a..p.b, G_annulus p t s * g s
  apply mul_pos p.hM
  apply intervalIntegral.integral_pos p.hab.2 hcont
  · intro s hs
    exact mul_nonneg (G_annulus_nonneg p t.2 ⟨hs.1.le, hs.2⟩)
      (div_nonneg (Real.rpow_nonneg (p.hf_pos _ (hφ _)).le _) (denominatorAnnulus_pos p φ hφ).le)
  · exact ⟨t, t.2, mul_pos (G_annulus_pos p ht ht)
      (div_pos (Real.rpow_pos_of_pos (p.hf_pos _ (hφ _)) _) (denominatorAnnulus_pos p φ hφ))⟩

lemma denominatorAnnulus_upper (p : AnnulusParams) (φ : EAnnulus p) (hφ : ∀ t, 0 ≤ φ t)
    {R : ℝ} (hR : 0 ≤ R) (hnorm : ‖φ‖ ≤ R) : denominatorAnnulus p φ ≤
      ((∫ s in p.a..p.b, p.pn * s ^ (p.n-1)) * p.f R)^p.β := by
  have hw : Continuous (fun s : ℝ => p.pn * s ^ (p.n-1)) := continuous_const.mul (continuous_id.pow _)
  have hc : Continuous (fun s => p.f (extendAnnulus p φ s)) := p.hf_cont.comp (extendAnnulus_continuous p φ)
  have hi : (∫ s in p.a..p.b, p.pn * s ^ (p.n-1) * p.f (extendAnnulus p φ s)) ≤
      ∫ s in p.a..p.b, p.pn * s ^ (p.n-1) * p.f R := by
    apply intervalIntegral.integral_mono_on p.hab.2.le
      ((hw.mul hc).intervalIntegrable _ _) ((hw.mul continuous_const).intervalIntegrable _ _)
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg p.hpn.le (pow_nonneg (lt_of_lt_of_le p.hab.1 hs.1).le _))
    apply p.hf_mono (hφ _) hR
    exact (le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm φ _).trans hnorm)
  rw [intervalIntegral.integral_mul_const] at hi
  exact Real.rpow_le_rpow (intervalIntegral.integral_nonneg p.hab.2.le (fun s hs =>
    mul_nonneg (mul_nonneg p.hpn.le (pow_nonneg (lt_of_lt_of_le p.hab.1 hs.1).le _))
      (p.hf_pos _ (hφ _)).le)) hi p.hβ.le

lemma denominatorAnnulus_cone_lower (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) (φ : EAnnulus p)
    (hφ : φ ∈ conePAnnulus p a₁ b₁ h) :
    (∫ s in a₁..b₁, p.pn * s ^ (p.n-1))^p.β *
      p.f (c_annulus p a₁ b₁ * ‖φ‖)^p.β ≤ denominatorAnnulus p φ := by
  let c := c_annulus p a₁ b₁
  have hc : 0 < c := (c_annulus_bounds p a₁ b₁ h).1
  have hw : Continuous (fun s : ℝ => p.pn * s ^ (p.n-1)) := continuous_const.mul (continuous_id.pow _)
  have hf : Continuous (fun s => p.f (extendAnnulus p φ s)) := p.hf_cont.comp (extendAnnulus_continuous p φ)
  have hi : (∫ s in a₁..b₁, p.pn * s ^ (p.n-1)) * p.f (c*‖φ‖) ≤
      ∫ s in a₁..b₁, p.pn * s ^ (p.n-1) * p.f (extendAnnulus p φ s) := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_mono_on h.2.1.le
      ((hw.mul continuous_const).intervalIntegrable _ _) ((hw.mul hf).intervalIntegrable _ _)
    intro s hs
    have hs' : s ∈ Icc p.a p.b := ⟨h.1.le.trans hs.1, hs.2.trans h.2.2.le⟩
    have hlow : c*‖φ‖ ≤ extendAnnulus p φ s := by
      simpa [extendAnnulus, projIcc_of_mem p.hab.2.le hs'] using hφ.2 s hs
    exact mul_le_mul_of_nonneg_left
      (p.hf_mono (mul_nonneg hc.le (norm_nonneg _)) (hφ.1 _) hlow)
      (mul_nonneg p.hpn.le (pow_nonneg (lt_of_lt_of_le p.hab.1 hs'.1).le _))
  have hj : (∫ s in a₁..b₁, p.pn * s ^ (p.n-1) * p.f (extendAnnulus p φ s)) ≤
      ∫ s in p.a..p.b, p.pn * s ^ (p.n-1) * p.f (extendAnnulus p φ s) := by
    apply intervalIntegral.integral_mono_interval h.1.le h.2.1.le h.2.2.le _
      ((hw.mul hf).intervalIntegrable _ _)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (mul_nonneg p.hpn.le (pow_nonneg (lt_trans p.hab.1 hs.1).le _))
      (p.hf_pos _ (hφ.1 _)).le
  have hwpos := annulus_weight_pos p (lt_trans p.hab.1 h.1) h.2.1
  rw [← Real.mul_rpow hwpos.le (p.hf_pos _ (mul_nonneg hc.le (norm_nonneg _))).le]
  exact Real.rpow_le_rpow (mul_nonneg hwpos.le
    (p.hf_pos _ (mul_nonneg hc.le (norm_nonneg _))).le) (hi.trans hj) p.hβ.le

/-- Theorem 3.1, with the general-β threshold and the cone fixed-point axiom. -/
theorem existence_annulus
    (p : AnnulusParams)
    (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b)
    (h_growth : ConditionAnnulus p a₁ b₁) :
    ∃ φ : EAnnulus p, IsPositiveRadialSolution p φ := by
  let W := ∫ s in p.a..p.b, p.pn * s ^ (p.n-1)
  have hW : 0 < W := annulus_weight_pos p p.hab.1 p.hab.2
  let d₁ := (W*p.f 1)^p.β
  let d₀ := (W*p.f 0)^p.β
  have hd₁ : 0 < d₁ := Real.rpow_pos_of_pos (mul_pos hW (p.hf_pos 1 zero_le_one)) _
  have hd₀ : 0 < d₀ := Real.rpow_pos_of_pos (mul_pos hW (p.hf_pos 0 le_rfl)) _
  let l := p.f 0 ^ p.α / d₁
  have hl : 0 < l := div_pos (Real.rpow_pos_of_pos (p.hf_pos 0 le_rfl) _) hd₁
  let t₀ : Icc p.a p.b := ⟨(p.a+p.b)/2, by constructor <;> linarith [p.hab.2]⟩
  let K₀ := ∫ s in p.a..p.b, G_annulus p t₀ s
  have hK₀ : 0 < K₀ := annulus_kernel_integral_pos p t₀ (by constructor <;> dsimp [t₀] <;> linarith [p.hab.2])
  let K := annulusGreenSup p
  have hK : 0 < K := annulusGreenSup_pos p
  let r := min 1 (p.M*l*K₀/2)
  have hr : 0 < r := lt_min zero_lt_one (div_pos (mul_pos (mul_pos p.hM hl) hK₀) (by norm_num))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrlo : r ≤ p.M*l*K₀ := (min_le_right _ _).trans (by nlinarith [mul_pos (mul_pos p.hM hl) hK₀])
  let c := c_annulus p a₁ b₁
  have hc : 0 < c ∧ c < 1 := c_annulus_bounds p a₁ b₁ h
  let V := (∫ s in a₁..b₁, p.pn * s ^ (p.n-1))^p.β
  have hV : 0 < V := Real.rpow_pos_of_pos (annulus_weight_pos p (lt_trans p.hab.1 h.1) h.2.1) _
  have hlarge : ∀ᶠ u : ℝ in atTop,
      (p.f u ^ p.α) / (u * (p.f (c*u) ^ p.β)) < V / (p.M*K) := by
    have hh := (eventually_lt_of_limsup_lt h_growth).mono fun u hu => EReal.coe_lt_coe_iff.mp hu
    simpa only [N_annulus, div_eq_mul_inv] using hh
  obtain ⟨U, hU⟩ := eventually_atTop.mp hlarge
  let R := max U (r+1)
  have hrR : r < R := lt_of_lt_of_le (by linarith : r < r+1) (le_max_right _ _)
  have hR : 0 < R := lt_trans hr hrR
  have hRat := hU R (le_max_left _ _)
  have hP : ∃ φ ∈ (conePAnnulusCone p a₁ b₁ h).carrier, φ ≠ 0 := by
    let φ : EAnnulus p := ContinuousMap.const _ 1
    have hn : ‖φ‖ ≤ 1 := (ContinuousMap.norm_le _ (by norm_num)).2 (by intro t; norm_num [φ])
    refine ⟨φ, ⟨by intro t; norm_num [φ], ?_⟩, ?_⟩
    · intro t ht
      change c*‖φ‖ ≤ 1
      nlinarith [norm_nonneg φ, hc.1, hc.2]
    · intro heq
      have hh := congrArg (fun ψ : EAnnulus p => ψ (leftPointAnnulus p)) heq
      norm_num [φ] at hh
  have hCC : CompletelyContinuousOn (SAnnulus p) (conePAnnulusCone p a₁ b₁ h).carrier :=
    ⟨(SAnnulus_completelyContinuous p).1.mono (fun _ h => h.1),
      fun A hA hB => (SAnnulus_completelyContinuous p).2 A (fun _ h => (hA h).1) hB⟩
  obtain ⟨φ, hφ, hfix, _⟩ := cone_fixedPoint_between_spheres (conePAnnulusCone p a₁ b₁ h) hP (SAnnulus p)
    (fun φ hφ => SAnnulus_maps_cone p a₁ b₁ h hφ) hCC hr hrR
    (by
      intro φ hφ hn
      have hdenup := denominatorAnnulus_upper p φ hφ.1 zero_le_one (hn.le.trans hr1)
      have hbounds : ∀ s ∈ Icc p.a p.b,
          l ≤ (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ ∧
          (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ ≤ p.f 1 ^ p.α / d₀ := by
        intro s hs
        have hs0 := hφ.1 (projIcc p.a p.b p.hab.2.le s)
        have hfs := p.hf_mono hs0 (show (1 : ℝ) ∈ Ici (0 : ℝ) from by norm_num)
          ((le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm φ _).trans (hn.le.trans hr1)))
        have hf0 := p.hf_mono (show (0 : ℝ) ∈ Ici (0 : ℝ) from by simp) hs0 hs0
        refine ⟨?_, ?_⟩
        · exact (div_le_div_of_nonneg_right
            (Real.rpow_le_rpow (p.hf_pos 0 le_rfl).le hf0 p.hα.le) hd₁.le).trans
            (div_le_div_of_nonneg_left (Real.rpow_nonneg (p.hf_pos _ hs0).le _)
              (denominatorAnnulus_pos p φ hφ.1) hdenup)
        · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (p.hf_pos _ hs0).le _)
            hd₀ (denominatorAnnulus_lower p φ hφ.1)).trans
            (div_le_div_of_nonneg_right (Real.rpow_le_rpow (p.hf_pos _ hs0).le hfs p.hα.le) hd₀.le)
      rw [hn]
      exact hrlo.trans (SAnnulus_norm_bounds p φ hφ.1 t₀ hl.le
        (div_nonneg (Real.rpow_nonneg (p.hf_pos 1 zero_le_one).le _) hd₀.le) hbounds).1)
    (by
      intro φ hφ hn
      let d := V * p.f (c*R)^p.β
      have hcR : 0 < c*R := mul_pos hc.1 hR
      have hfb : 0 < p.f (c*R)^p.β := Real.rpow_pos_of_pos (p.hf_pos _ hcR.le) _
      have hd : 0 < d := mul_pos hV hfb
      have hden : d ≤ denominatorAnnulus p φ := by
        simpa only [hn] using denominatorAnnulus_cone_lower p a₁ b₁ h φ hφ
      have hbounds : ∀ s ∈ Icc p.a p.b,
          0 ≤ (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ ∧
          (p.f (extendAnnulus p φ s) ^ p.α) / denominatorAnnulus p φ ≤ p.f R ^ p.α / d := by
        intro s hs
        have hs0 := hφ.1 (projIcc p.a p.b p.hab.2.le s)
        have hfs := p.hf_mono hs0 hR.le
          ((le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm φ _).trans hn.le))
        refine ⟨div_nonneg (Real.rpow_nonneg (p.hf_pos _ hs0).le _) (denominatorAnnulus_pos p φ hφ.1).le, ?_⟩
        exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (p.hf_pos _ hs0).le _) hd hden).trans
          (div_le_div_of_nonneg_right (Real.rpow_le_rpow (p.hf_pos _ hs0).le hfs p.hα.le) hd.le)
      have hnum : p.f R^p.α * (p.M*K) < V*(R*p.f (c*R)^p.β) :=
        (div_lt_div_iff₀ (mul_pos hR hfb) (mul_pos p.hM hK)).mp hRat
      have hbound : p.M * (p.f R ^ p.α / d) * K ≤ R := by
        calc
          _ = (p.f R^p.α * (p.M*K))/d := by ring
          _ ≤ R := (div_le_iff₀ hd).2 (by dsimp [d]; nlinarith)
      exact (SAnnulus_norm_bounds p φ hφ.1 t₀ (le_refl 0)
        (div_nonneg (Real.rpow_nonneg (p.hf_pos R hR.le).le _) hd.le) hbounds).2.trans
        (by simpa only [hn] using hbound))
  refine ⟨φ, ?_, ?_, ?_, hfix⟩
  · intro t ht
    rw [← hfix]
    exact SAnnulus_strictlyPositive p φ hφ.1 t ht
  · rw [← hfix]
    exact (SAnnulus_boundary p φ).1
  · rw [← hfix]
    exact (SAnnulus_boundary p φ).2

/-- The fixed point supplied by Theorem 2.2 is a classical positive BVP solution. -/
theorem existence_classical_1D (p : Problem1DParams) (b : ℝ) (hb : 0 < b ∧ b < 1)
    (hA : ConditionA1D p b) :
    ∃ φ : E1D, IsPositiveSolution1D p φ ∧ IsClassicalSolution1D p φ := by
  obtain ⟨φ, hφ⟩ := existence_1D p b hb hA
  have hnn : ∀ t, 0 ≤ φ t := by
    intro t
    by_cases ht : t.1 < 1
    · exact (hφ.1 t ht).le
    · have heq : t = onePoint1D := Subtype.ext (le_antisymm t.2.2 (le_of_not_gt ht))
      rw [heq, hφ.2.1]
  exact ⟨φ, hφ, (BVP2_iff_fixedPoint p φ hnn).mpr hφ.2.2⟩

/-- The fixed point supplied by Theorem 3.1 is a classical positive radial BVP solution. -/
theorem existence_classical_annulus (p : AnnulusParams) (a₁ b₁ : ℝ)
    (h : p.a < a₁ ∧ a₁ < b₁ ∧ b₁ < p.b) (hg : ConditionAnnulus p a₁ b₁) :
    ∃ φ : EAnnulus p, IsPositiveRadialSolution p φ ∧ IsClassicalRadialSolution p φ := by
  obtain ⟨φ, hφ⟩ := existence_annulus p a₁ b₁ h hg
  have hnn : ∀ t, 0 ≤ φ t := by
    intro t
    by_cases hl : p.a < t.1
    · by_cases hr : t.1 < p.b
      · exact (hφ.1 t ⟨hl, hr⟩).le
      · have heq : t = rightPointAnnulus p := Subtype.ext (le_antisymm t.2.2 (le_of_not_gt hr))
        rw [heq, hφ.2.2.1]
    · have heq : t = leftPointAnnulus p := Subtype.ext (le_antisymm (le_of_not_gt hl) t.2.1)
      rw [heq, hφ.2.1]
  exact ⟨φ, hφ, (BVP12_iff_fixedPoint p φ hnn).mpr hφ.2.2.2⟩

/-! ## 4. Remarks from the paper, represented as formal metadata/propositions -/

/-- Remark 1 records the obstruction identified in the paper for a ball in dimension
`n ≥ 3`: the radial Green-function building block `1 - t^(2-n)` is unbounded near
zero.  This proposition is a direct asymptotic formulation of that observation. -/
theorem radial_ball_kernel_unbounded_near_zero (n : ℕ) (hn : 3 ≤ n) :
    ¬ Bornology.IsBounded (Set.range (fun t : Ioo (0 : ℝ) 1 =>
      1 - (t.1 ^ ((2 : ℝ) - (n : ℝ))))) := by
  intro hbounded
  obtain ⟨C, hC⟩ := hbounded.bddBelow
  let u : ℝ := max 2 (2 - C)
  have hu2 : 2 ≤ u := le_max_left _ _
  have huC : 2 - C ≤ u := le_max_right _ _
  have hu : 0 < u := by linarith
  have ht0 : 0 < u⁻¹ := inv_pos.mpr hu
  have ht1 : u⁻¹ < 1 := (inv_lt_one₀ hu).2 (by linarith)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (1 : ℝ) ≤ (n : ℝ) - 2 := by linarith
  have hpow : u ≤ u ^ ((n : ℝ) - 2) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ u) hk
  have hexp : (2 : ℝ) - (n : ℝ) = -((n : ℝ) - 2) := by ring
  have hlower := hC (Set.mem_range_self (⟨u⁻¹, ht0, ht1⟩ : Ioo (0 : ℝ) 1))
  dsimp at hlower
  rw [hexp, Real.rpow_neg_eq_inv_rpow, inv_inv] at hlower
  linarith

/-- Remark 2: the exterior-domain variant assumes the radial weight satisfies
`∫₁^∞ h(r) r^(n-1) dr < ∞`.  Integrability on `Ici 1` records this hypothesis. -/
def ExteriorWeightIntegrable (n : ℕ) (h : ℝ → ℝ) : Prop :=
  MeasureTheory.IntegrableOn (fun r => h r * r ^ (n - 1)) (Ici 1)

/-- Remark 3: the paper notes that cone expansion can also be used, provided the
nonlinearity is extended to `u=0`.  This is kept as a source-level marker because no
specific extension is fixed in the article. -/
def HasExtensionAtZero (f : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, ∀ u, 0 < u → g u = f u

end Stanczy2001
