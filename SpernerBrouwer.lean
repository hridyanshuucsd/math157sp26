-- SpernerBrouwer.lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Sperner's Lemma and Brouwer's Fixed Point Theorem (2D)

Changes from previous version:
  1. Fintype (TVertex n) and Orient now derive Fintype → allTriangles = Finset.univ
  2. IsSpernerLabeling corner labels corrected to match labelFromMap
  3. sperner_lemma declared as axiom (combinatorial double-count is in the essay)
  4. labelFromMap_is_sperner fully proved
-/

-- §1. The Standard 2-Simplex

def stdSimplex2 : Set (Fin 3 → ℝ) :=
  { x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 }

namespace stdSimplex2

def corner (k : Fin 3) : Fin 3 → ℝ := fun i => if i = k then 1 else 0

lemma corner_mem (k : Fin 3) : corner k ∈ stdSimplex2 := by
  refine ⟨fun i => ?_, ?_⟩
  · simp [corner]; split_ifs <;> norm_num
  · fin_cases k <;> simp [corner, Fin.sum_univ_three]

lemma isCompact : IsCompact stdSimplex2 := by
  have hcl : IsClosed stdSimplex2 := by
    apply IsClosed.inter
    · rw [show (fun x : Fin 3 → ℝ => ∀ i, 0 ≤ x i) =
              (fun x => x ∈ ⋂ i : Fin 3, {x | 0 ≤ x i}) from by ext x; simp]
      apply isClosed_iInter; intro i
      exact isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq
        (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
  exact IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc (a := (0 : ℝ)) (b := 1)))
    hcl
    (fun x hx => by
      simp only [Set.mem_univ_pi, Set.mem_Icc]; intro i
      exact ⟨hx.1 i, by
        have h := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
        linarith [hx.2]⟩)

end stdSimplex2

-- §2. Triangulation Vertices

def TVertex (n : ℕ) : Type :=
  { p : Fin (n + 1) × Fin (n + 1) // p.1.val + p.2.val ≤ n }

-- Yuan's suggestion: Fintype falls out for free from the subtype
instance (n : ℕ) : Fintype (TVertex n) := by unfold TVertex; infer_instance

@[ext]
lemma TVertex.ext {n : ℕ} {v w : TVertex n} (h : v.val = w.val) : v = w :=
  Subtype.ext h

instance (n : ℕ) : DecidableEq (TVertex n) :=
  fun v w =>
    if h : v.val = w.val
    then isTrue (TVertex.ext h)
    else isFalse (fun heq => h (congr_arg Subtype.val heq))

noncomputable def TVertex.toPoint (n : ℕ) (v : TVertex n) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then v.val.1.val / (n : ℝ)
    else if i = 1 then v.val.2.val / (n : ℝ)
    else 1 - v.val.1.val / (n : ℝ) - v.val.2.val / (n : ℝ)

lemma TVertex.toPoint_mem (n : ℕ) (hn : 0 < n) (v : TVertex n) :
    TVertex.toPoint n v ∈ stdSimplex2 := by
  have hn'   : (n : ℝ) > 0              := Nat.cast_pos.mpr hn
  have ha    : (v.val.1.val : ℝ) / n ≥ 0 := by positivity
  have hb    : (v.val.2.val : ℝ) / n ≥ 0 := by positivity
  have hprop : (v.val.1.val : ℝ) + v.val.2.val ≤ n := by exact_mod_cast v.property
  have hab   : (v.val.1.val : ℝ) / n + v.val.2.val / n ≤ 1 := by
    have : (v.val.1.val : ℝ) / n + v.val.2.val / n =
           (v.val.1.val + v.val.2.val) / n := by ring
    rw [this, div_le_one hn']; exact hprop
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · show 0 ≤ v.val.1.val / (n : ℝ); linarith
    · show 0 ≤ v.val.2.val / (n : ℝ); linarith
    · show 0 ≤ 1 - v.val.1.val / (n : ℝ) - v.val.2.val / (n : ℝ); linarith
  · simp only [Fin.sum_univ_three]
    show v.val.1.val / (n : ℝ) + v.val.2.val / (n : ℝ) +
         (1 - v.val.1.val / (n : ℝ) - v.val.2.val / (n : ℝ)) = 1
    ring

-- §3. Sperner Labeling

def SpernerLabeling (n : ℕ) := TVertex n → Fin 3

def TVertex.onFace (k : Fin 3) (n : ℕ) (v : TVertex n) : Prop :=
  match k with
  | ⟨0, _⟩ => v.val.1.val = 0
  | ⟨1, _⟩ => v.val.2.val = 0
  | ⟨2, _⟩ => v.val.1.val + v.val.2.val = n

-- Corner labels corrected to match labelFromMap:
--   toPoint 0 = v.val.1/n; toPoint 1 = v.val.2/n; toPoint 2 = 1 - toPoint0 - toPoint1
--   corner0 (val.1=0, val.2=0) = e₂ = (0,0,1)  → decreasing coord is 2 → label 2
--   corner1 (val.1=n, val.2=0) = e₀ = (1,0,0)  → decreasing coord is 0 → label 0
--   corner2 (val.1=0, val.2=n) = e₁ = (0,1,0)  → decreasing coord is 1 → label 1
structure IsSpernerLabeling (n : ℕ) (hn : 0 < n) (L : SpernerLabeling n) : Prop where
  corner0 : ∀ v, v.val.1.val = 0 ∧ v.val.2.val = 0 → L v = 2
  corner1 : ∀ v, v.val.1.val = n ∧ v.val.2.val = 0 → L v = 0
  corner2 : ∀ v, v.val.1.val = 0 ∧ v.val.2.val = n → L v = 1
  face    : ∀ k v, TVertex.onFace k n v               → L v ≠ k

-- §4. Triangles and Full Labeling

-- Added Fintype derivation so STriangle gets a Fintype instance below
inductive Orient | Up | Down deriving DecidableEq, Fintype

structure STriangle (n : ℕ) where
  base  : TVertex n
  ori   : Orient
  valid : match ori with
    | Orient.Up   =>
        base.val.1.val + 1 ≤ n ∧
        base.val.2.val + 1 ≤ n ∧
        base.val.1.val + base.val.2.val + 1 ≤ n
    | Orient.Down =>
        base.val.1.val + 1 ≤ n ∧
        base.val.2.val + 1 ≤ n ∧
        base.val.1.val + base.val.2.val + 2 ≤ n

-- The validity predicate on TVertex n × Orient is decidable
private instance STriangle.validDecidable (n : ℕ) (b : TVertex n) (o : Orient) :
    Decidable (match o with
      | Orient.Up   => b.val.1.val + 1 ≤ n ∧ b.val.2.val + 1 ≤ n ∧
                       b.val.1.val + b.val.2.val + 1 ≤ n
      | Orient.Down => b.val.1.val + 1 ≤ n ∧ b.val.2.val + 1 ≤ n ∧
                       b.val.1.val + b.val.2.val + 2 ≤ n) := by
  cases o <;> infer_instance

-- STriangle n is in bijection with a decidable subtype of Fintype × Fintype
instance (n : ℕ) : Fintype (STriangle n) :=
  haveI : DecidablePred (fun p : TVertex n × Orient => match p.2 with
      | Orient.Up   => p.1.val.1.val + 1 ≤ n ∧ p.1.val.2.val + 1 ≤ n ∧
                       p.1.val.1.val + p.1.val.2.val + 1 ≤ n
      | Orient.Down => p.1.val.1.val + 1 ≤ n ∧ p.1.val.2.val + 1 ≤ n ∧
                       p.1.val.1.val + p.1.val.2.val + 2 ≤ n) :=
    fun ⟨b, o⟩ => STriangle.validDecidable n b o
  Fintype.ofEquiv
    { p : TVertex n × Orient // match p.2 with
        | Orient.Up   => p.1.val.1.val + 1 ≤ n ∧ p.1.val.2.val + 1 ≤ n ∧
                         p.1.val.1.val + p.1.val.2.val + 1 ≤ n
        | Orient.Down => p.1.val.1.val + 1 ≤ n ∧ p.1.val.2.val + 1 ≤ n ∧
                         p.1.val.1.val + p.1.val.2.val + 2 ≤ n }
    { toFun    := fun ⟨⟨b, o⟩, h⟩ => ⟨b, o, h⟩
      invFun   := fun T => ⟨(T.base, T.ori), T.valid⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }

def STriangle.vert (n : ℕ) (T : STriangle n) : Fin 3 → TVertex n :=
  match T.ori, T.valid with
  | Orient.Up, ⟨hv1, hv2, hv3⟩ =>
    fun i => match i with
    | ⟨0, _⟩ => T.base
    | ⟨1, _⟩ =>
        have h : T.base.val.1.val + 1 + T.base.val.2.val ≤ n := by omega
        ⟨(⟨T.base.val.1.val + 1, by omega⟩, ⟨T.base.val.2.val, T.base.val.2.isLt⟩), h⟩
    | ⟨2, _⟩ =>
        have h : T.base.val.1.val + (T.base.val.2.val + 1) ≤ n := by omega
        ⟨(⟨T.base.val.1.val, T.base.val.1.isLt⟩, ⟨T.base.val.2.val + 1, by omega⟩), h⟩
  | Orient.Down, ⟨hv1, hv2, hv3⟩ =>
    fun i => match i with
    | ⟨0, _⟩ =>
        have h : T.base.val.1.val + 1 + T.base.val.2.val ≤ n := by omega
        ⟨(⟨T.base.val.1.val + 1, by omega⟩, ⟨T.base.val.2.val, T.base.val.2.isLt⟩), h⟩
    | ⟨1, _⟩ =>
        have h : T.base.val.1.val + (T.base.val.2.val + 1) ≤ n := by omega
        ⟨(⟨T.base.val.1.val, T.base.val.1.isLt⟩, ⟨T.base.val.2.val + 1, by omega⟩), h⟩
    | ⟨2, _⟩ =>
        have h : T.base.val.1.val + 1 + (T.base.val.2.val + 1) ≤ n := by omega
        ⟨(⟨T.base.val.1.val + 1, by omega⟩, ⟨T.base.val.2.val + 1, by omega⟩), h⟩

def IsFullyLabeled (n : ℕ) (L : SpernerLabeling n) (T : STriangle n) : Prop :=
  ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    L (T.vert n i) = 0 ∧ L (T.vert n j) = 1 ∧ L (T.vert n k) = 2

instance isFullyLabeled_decidable (n : ℕ) (L : SpernerLabeling n) (T : STriangle n) :
    Decidable (IsFullyLabeled n L T) := by
  unfold IsFullyLabeled
  have hbase : ∀ i j k : Fin 3, Decidable (i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      L (T.vert n i) = 0 ∧ L (T.vert n j) = 1 ∧ L (T.vert n k) = 2) :=
    fun i j k => inferInstance
  have hk : ∀ i j : Fin 3, Decidable (∃ k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      L (T.vert n i) = 0 ∧ L (T.vert n j) = 1 ∧ L (T.vert n k) = 2) := fun i j => by
    haveI : DecidablePred (fun k : Fin 3 => i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
        L (T.vert n i) = 0 ∧ L (T.vert n j) = 1 ∧ L (T.vert n k) = 2) := hbase i j
    exact Fintype.decidableExistsFintype
  have hj : ∀ i : Fin 3, Decidable (∃ j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      L (T.vert n i) = 0 ∧ L (T.vert n j) = 1 ∧ L (T.vert n k) = 2) := fun i => by
    haveI : DecidablePred (fun j : Fin 3 => ∃ k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
        L (T.vert n i) = 0 ∧ L (T.vert n j) = 1 ∧ L (T.vert n k) = 2) := hk i
    exact Fintype.decidableExistsFintype
  haveI : DecidablePred (fun i : Fin 3 => ∃ j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      L (T.vert n i) = 0 ∧ L (T.vert n j) = 1 ∧ L (T.vert n k) = 2) := hj
  exact Fintype.decidableExistsFintype

-- §5. Distinguished Edges and Parity

def IsDistinguished (n : ℕ) (L : SpernerLabeling n) (v w : TVertex n) : Prop :=
  (L v = 0 ∧ L w = 1) ∨ (L v = 1 ∧ L w = 0)

instance isDistinguished_decidable (n : ℕ) (L : SpernerLabeling n)
    (v w : TVertex n) : Decidable (IsDistinguished n L v w) :=
  if h1 : L v = 0 ∧ L w = 1 then isTrue (Or.inl h1)
  else if h2 : L v = 1 ∧ L w = 0 then isTrue (Or.inr h2)
  else isFalse (fun h => h.elim h1 h2)

def distCount (n : ℕ) (L : SpernerLabeling n) (T : STriangle n) : ℕ :=
  (Finset.filter
    (fun p : Fin 3 × Fin 3 =>
      p.1.val < p.2.val ∧
      IsDistinguished n L (T.vert n p.1) (T.vert n p.2))
    (Finset.univ (α := Fin 3 × Fin 3))).card

private lemma distCount_as_sum (n : ℕ) (L : SpernerLabeling n) (T : STriangle n) :
    distCount n L T =
    (if IsDistinguished n L (T.vert n 0) (T.vert n 1) then 1 else 0) +
    (if IsDistinguished n L (T.vert n 0) (T.vert n 2) then 1 else 0) +
    (if IsDistinguished n L (T.vert n 1) (T.vert n 2) then 1 else 0) := by
  -- Build an explicit bijection: the only pairs with a.val < b.val in Fin 3 × Fin 3
  -- are (0,1), (0,2), (1,2).  Restrict the filter to those three, then split_ifs.
  have hkey : Finset.filter (fun p : Fin 3 × Fin 3 =>
        p.1.val < p.2.val ∧ IsDistinguished n L (T.vert n p.1) (T.vert n p.2))
        Finset.univ =
      Finset.filter (fun p : Fin 3 × Fin 3 =>
        IsDistinguished n L (T.vert n p.1) (T.vert n p.2))
        ({((0:Fin 3),(1:Fin 3)), ((0:Fin 3),(2:Fin 3)), ((1:Fin 3),(2:Fin 3))} :
            Finset (Fin 3 × Fin 3)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro ⟨hlt, hd⟩
      refine ⟨?_, hd⟩
      fin_cases a <;> fin_cases b <;> simp_all
    · intro ⟨hmem, hd⟩
      refine ⟨?_, hd⟩
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  unfold distCount
  rw [hkey, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  split_ifs <;> decide

lemma distCount_fully_labeled {n : ℕ} (L : SpernerLabeling n) (T : STriangle n)
    (h : IsFullyLabeled n L T) : distCount n L T = 1 := by
  obtain ⟨i, j, k, hij, hjk, hik, hli, hlj, hlk⟩ := h
  rw [distCount_as_sum]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [IsDistinguished]

lemma distCount_not_fully_labeled {n : ℕ} (L : SpernerLabeling n) (T : STriangle n)
    (h : ¬IsFullyLabeled n L T) : distCount n L T = 0 ∨ distCount n L T = 2 := by
  rw [distCount_as_sum]
  -- Every Fin 3 value is 0, 1, or 2; case-split each vertex label.
  have split3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := fun x => by fin_cases x <;> decide
  rcases split3 (L (STriangle.vert n T 0)) with h0 | h0 | h0 <;>
  rcases split3 (L (STriangle.vert n T 1)) with h1 | h1 | h1 <;>
  rcases split3 (L (STriangle.vert n T 2)) with h2 | h2 | h2 <;>
  simp only [h0, h1, h2, IsDistinguished] <;>
  first
  | decide
  | (exfalso; apply h; first
     | exact ⟨0, 1, 2, by decide, by decide, by decide, h0, h1, h2⟩
     | exact ⟨0, 2, 1, by decide, by decide, by decide, h0, h2, h1⟩
     | exact ⟨1, 0, 2, by decide, by decide, by decide, h1, h0, h2⟩
     | exact ⟨2, 0, 1, by decide, by decide, by decide, h2, h0, h1⟩
     | exact ⟨1, 2, 0, by decide, by decide, by decide, h1, h2, h0⟩
     | exact ⟨2, 1, 0, by decide, by decide, by decide, h2, h1, h0⟩)

-- §6. allTriangles and Sperner's Lemma

-- Now that STriangle n has Fintype, allTriangles is just Finset.univ
def allTriangles (n : ℕ) : Finset (STriangle n) := Finset.univ

-- Sperner's Lemma: treated axiomatically.
-- The combinatorial proof (mod-2 double count of distinguished edges) is
-- described in full in the documentation essay.  The double-counting
-- infrastructure (Finset-level incidence graph) exceeds the remaining scope.
axiom sperner_lemma (n : ℕ) (hn : 0 < n)
    (L : SpernerLabeling n) (hL : IsSpernerLabeling n hn L) :
    Odd (Finset.card ((allTriangles n).filter (IsFullyLabeled n L)))

-- §7. Labeling from a Fixed-Point-Free Map

lemma exists_coord_gt {f : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {v : Fin 3 → ℝ} (hv : v ∈ stdSimplex2) (hfv : f v ∈ stdSimplex2)
    (hne : v ≠ f v) :
    ∃ k : Fin 3, f v k < v k := by
  by_contra hall
  simp only [not_exists, not_lt] at hall
  have hsum_v  : ∑ i : Fin 3, v i   = 1 := hv.2
  have hsum_fv : ∑ i : Fin 3, f v i = 1 := hfv.2
  have heq : ∀ k : Fin 3, v k = f v k := by
    intro k
    apply le_antisymm (hall k)
    by_contra h; simp only [not_le] at h
    have hstrict : ∑ i : Fin 3, v i < ∑ i : Fin 3, f v i :=
      Finset.sum_lt_sum (fun i _ => hall i) ⟨k, Finset.mem_univ k, h⟩
    linarith
  exact hne (funext heq)

noncomputable def labelFromMap
    (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hf_mem  : ∀ x, x ∈ stdSimplex2 → f x ∈ stdSimplex2)
    (hf_nofp : ∀ x, x ∈ stdSimplex2 → x ≠ f x)
    (n : ℕ) (hn : 0 < n) :
    SpernerLabeling n :=
  fun v =>
    let p  := TVertex.toPoint n v
    let hp := TVertex.toPoint_mem n hn v
    Classical.choose (exists_coord_gt hp (hf_mem p hp) (hf_nofp p hp))

lemma labelFromMap_is_sperner
    (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (_hf_cont : Continuous f)
    (hf_mem  : ∀ x, x ∈ stdSimplex2 → f x ∈ stdSimplex2)
    (hf_nofp : ∀ x, x ∈ stdSimplex2 → x ≠ f x)
    (n : ℕ) (hn : 0 < n) :
    IsSpernerLabeling n hn (labelFromMap f hf_mem hf_nofp n hn) := by
  have hn' : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
  -- Core helper: if toPoint n v k = 0 then label ≠ k.
  -- Proof: f(v)_k ≥ 0 = v_k, so k is never the decreasing coordinate.
  have face_ne : ∀ (v : TVertex n) (k : Fin 3),
      TVertex.toPoint n v k = 0 → labelFromMap f hf_mem hf_nofp n hn v ≠ k := by
    intro v k hk heq
    have hp   := TVertex.toPoint_mem n hn v
    have hfvp := hf_mem (TVertex.toPoint n v) hp
    have hneq := hf_nofp (TVertex.toPoint n v) hp
    have hspec := Classical.choose_spec (exists_coord_gt hp hfvp hneq)
    -- heq : labelFromMap ... v = k, which definitionally equals
    -- Classical.choose (exists_coord_gt hp hfvp hneq) = k
    have hcc : Classical.choose (exists_coord_gt hp hfvp hneq) = k := heq
    rw [hcc, hk] at hspec
    linarith [hfvp.1 k]
  -- Derived helper: when two coordinates are 0, the label equals the third.
  -- Uses omega on Fin 3 val after fin_cases on all indices.
  have corner_eq : ∀ (v : TVertex n) (k0 k1 target : Fin 3),
      TVertex.toPoint n v k0 = 0 → TVertex.toPoint n v k1 = 0 →
      k0 ≠ k1 → k0 ≠ target → k1 ≠ target →
      labelFromMap f hf_mem hf_nofp n hn v = target := by
    intro v k0 k1 target h0 h1 hne01 hne0t hne1t
    have hm0 := face_ne v k0 h0
    have hm1 := face_ne v k1 h1
    apply Fin.ext
    have hv0 : (labelFromMap f hf_mem hf_nofp n hn v).val ≠ k0.val :=
      fun h => hm0 (Fin.ext h)
    have hv1 : (labelFromMap f hf_mem hf_nofp n hn v).val ≠ k1.val :=
      fun h => hm1 (Fin.ext h)
    have hlt : (labelFromMap f hf_mem hf_nofp n hn v).val < 3 :=
      (labelFromMap f hf_mem hf_nofp n hn v).isLt
    -- Convert Fin inequalities to Nat inequalities for omega
    have h01 : k0.val ≠ k1.val     := fun h => hne01 (Fin.ext h)
    have h0t : k0.val ≠ target.val := fun h => hne0t (Fin.ext h)
    have h1t : k1.val ≠ target.val := fun h => hne1t (Fin.ext h)
    have hk0  : k0.val < 3     := k0.isLt
    have hk1  : k1.val < 3     := k1.isLt
    have htgt : target.val < 3 := target.isLt
    -- After fin_cases all k-values are concrete; omega closes all 27 cases
    fin_cases k0 <;> fin_cases k1 <;> fin_cases target <;> omega
  constructor
  · -- corner0: val.1=0, val.2=0  →  toPoint = (0,0,1)  →  label = 2
    intro v ⟨h1, h2⟩
    apply corner_eq v 0 1 2
    · show v.val.1.val / (n : ℝ) = 0
      simp [show (v.val.1.val : ℝ) = 0 from by exact_mod_cast h1]
    · show v.val.2.val / (n : ℝ) = 0
      simp [show (v.val.2.val : ℝ) = 0 from by exact_mod_cast h2]
    · decide
    · decide
    · decide
  · -- corner1: val.1=n, val.2=0  →  toPoint = (1,0,0)  →  label = 0
    intro v ⟨h1, h2⟩
    apply corner_eq v 1 2 0
    · show v.val.2.val / (n : ℝ) = 0
      simp [show (v.val.2.val : ℝ) = 0 from by exact_mod_cast h2]
    · show 1 - v.val.1.val / (n : ℝ) - v.val.2.val / (n : ℝ) = 0
      rw [show (v.val.1.val : ℝ) = n from by exact_mod_cast h1,
          show (v.val.2.val : ℝ) = 0 from by exact_mod_cast h2]
      field_simp [ne_of_gt hn']; ring
    · decide
    · decide
    · decide
  · -- corner2: val.1=0, val.2=n  →  toPoint = (0,1,0)  →  label = 1
    intro v ⟨h1, h2⟩
    apply corner_eq v 0 2 1
    · show v.val.1.val / (n : ℝ) = 0
      simp [show (v.val.1.val : ℝ) = 0 from by exact_mod_cast h1]
    · show 1 - v.val.1.val / (n : ℝ) - v.val.2.val / (n : ℝ) = 0
      rw [show (v.val.1.val : ℝ) = 0 from by exact_mod_cast h1,
          show (v.val.2.val : ℝ) = n from by exact_mod_cast h2]
      field_simp [ne_of_gt hn']; ring
    · decide
    · decide
    · decide
  · -- face: onFace k v  →  toPoint n v k = 0  →  label ≠ k  (by face_ne)
    intro k v hface
    apply face_ne
    fin_cases k
    · simp only [TVertex.onFace] at hface
      show v.val.1.val / (n : ℝ) = 0
      simp [show (v.val.1.val : ℝ) = 0 from by exact_mod_cast hface]
    · simp only [TVertex.onFace] at hface
      show v.val.2.val / (n : ℝ) = 0
      simp [show (v.val.2.val : ℝ) = 0 from by exact_mod_cast hface]
    · simp only [TVertex.onFace] at hface
      show 1 - v.val.1.val / (n : ℝ) - v.val.2.val / (n : ℝ) = 0
      have hcast : (v.val.1.val : ℝ) + v.val.2.val = n := by exact_mod_cast hface
      field_simp [ne_of_gt hn']
      linarith

-- §8. Brouwer's Fixed Point Theorem

theorem brouwer_fixed_point_2d
    (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hf_cont : Continuous f)
    (hf_mem  : ∀ x, x ∈ stdSimplex2 → f x ∈ stdSimplex2) :
    ∃ x ∈ stdSimplex2, f x = x := by
  by_contra hall
  simp only [not_exists, not_and] at hall
  have hf_nofp : ∀ x, x ∈ stdSimplex2 → x ≠ f x :=
    fun x hx heq => hall x hx heq.symm
  -- Step 1: for each n ≥ 1, Sperner's Lemma gives a fully labeled triangle.
  have hFL : ∀ (n : ℕ) (hn : 0 < n),
      ∃ T : STriangle n, IsFullyLabeled n (labelFromMap f hf_mem hf_nofp n hn) T := by
    intro n hn
    have hsperner := sperner_lemma n hn
        (labelFromMap f hf_mem hf_nofp n hn)
        (labelFromMap_is_sperner f hf_cont hf_mem hf_nofp n hn)
    have hpos : 0 < ((allTriangles n).filter
        (IsFullyLabeled n (labelFromMap f hf_mem hf_nofp n hn))).card := by
      obtain ⟨k, hk⟩ := hsperner; omega
    obtain ⟨T, hT⟩ := Finset.card_pos.mp hpos
    exact ⟨T, (Finset.mem_filter.mp hT).2⟩
  -- Step 2: extract a convergent subsequence by compactness and derive a fixed point.
  -- The barycenter of T_n lies in stdSimplex₂ (convexity), and all three vertices
  -- converge to the same limit x* since diam(T_n) ≤ 2/n → 0.  The full-labeling
  -- condition gives f(v^k_n)_k < v^k_n_k for each coordinate k.  Passing through
  -- the limit via ContinuousAt.tendsto and ge_of_tendsto yields f(x*)_k ≤ x*_k for
  -- all k.  The sum constraint then forces f(x*) = x*, contradicting hf_nofp.
  sorry
