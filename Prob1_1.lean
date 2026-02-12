-- 以下为旧版大规模形式化，恢复并修复。
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Sort
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

open Finset Function List

-- 兼容旧版接口的辅助引理
namespace List
lemma nodup_iff_perm_nodup {α : Type*} {l₁ l₂ : List α} (h : l₁ ~ l₂) :
    l₁.Nodup ↔ l₂.Nodup :=
  (List.Perm.nodup_iff h)

lemma mem_of_perm {α : Type*} {l₁ l₂ : List α} (h : l₁ ~ l₂) {x : α} :
    x ∈ l₁ → x ∈ l₂ := by
  intro hx
  exact (List.Perm.mem_iff h).1 hx

lemma nodup_take_of_nodup {α : Type*} {l : List α} (h : l.Nodup) (n : ℕ) :
    (l.take n).Nodup := by
  classical
  apply (List.nodup_iff_sublist).2
  intro a ha
  have hsub : [a, a] <+ l := (List.Sublist.trans ha (List.take_sublist n l))
  exact (List.nodup_iff_sublist).1 h a hsub

lemma mem_take {α : Type*} {l : List α} {n : ℕ} {x : α} :
    x ∈ l.take n ↔ ∃ i, i < n ∧ ∃ hi : i < l.length, l.get ⟨i, hi⟩ = x := by
  constructor
  · intro hx
    rcases (List.mem_iff_getElem).1 hx with ⟨i, hi, hxi⟩
    have hlen : (l.take n).length = min n l.length := by
      simpa using (List.length_take (l := l) (n := n))
    have hi_min : i < min n l.length := by simpa [hlen] using hi
    have hi_n : i < n := (lt_min_iff.mp hi_min).1
    have hi_len : i < l.length := (lt_min_iff.mp hi_min).2
    have hxi' : l.get ⟨i, hi_len⟩ = x := by
      -- 由 take 的索引还原到原列表
      simpa [List.getElem_take] using hxi
    exact ⟨i, hi_n, hi_len, hxi'⟩
  · rintro ⟨i, hi_n, hi_len, hxi⟩
    have hi' : i < (l.take n).length := by
      have hlen : (l.take n).length = min n l.length := by
        simpa using (List.length_take (l := l) (n := n))
      have hi_min : i < min n l.length := (lt_min_iff.mpr ⟨hi_n, hi_len⟩)
      exact (by simpa [hlen] using hi_min)
    exact (List.mem_iff_getElem).2 ⟨i, hi', by simpa [List.getElem_take] using hxi⟩

end List

namespace Finset
lemma card_inter_le {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s ∩ t).card ≤ s.card := by
  exact Finset.card_le_card (Finset.inter_subset_left)

lemma mem_of_mem_sdiff {α : Type*} [DecidableEq α] {s t : Finset α} {x : α} :
    x ∈ s \ t → x ∈ s := by
  intro hx
  exact (Finset.mem_sdiff.mp hx).1

lemma not_mem_sdiff_of_mem {α : Type*} [DecidableEq α] {s t : Finset α} {x : α} :
    x ∈ t → x ∉ s \ t := by
  intro hx hs
  exact (Finset.mem_sdiff.mp hs).2 hx
end Finset

/-- 问题的基本设置：8个学生，3个科目 -/
structure CompetitionSetup (Student : Type*) (Subject : Type*)
  [Fintype Student] [DecidableEq Student]
  [Fintype Subject] [DecidableEq Subject] where
  (student_count : Fintype.card Student = 8)
  (subject_count : Fintype.card Subject = 3)
  -- 分数函数：给定科目和学生，返回分数（自然数）
  (score : Subject → Student → ℕ)
  -- 条件：每个科目的学生分数各不相同
  (score_injective : ∀ s : Subject, Injective (score s))

namespace CompetitionSetup

noncomputable section
open Classical

variable {Student Subject : Type*} [Fintype Student] [DecidableEq Student]
variable [Fintype Subject] [DecidableEq Subject]


/-- 计算 TopHalf 的函数。
    根据分数对当前学生进行排序，并取前一半。-/
def computeTopHalf (setup : CompetitionSetup Student Subject) (sub : Subject) (current : Finset Student) : Finset Student :=
  let sorted := (current.toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b)))
  (sorted.take (current.card / 2)).toFinset

-- (旧版 List.Nodup.take 已由 List.nodup_take_of_nodup 代替)

lemma computeTopHalf_card (setup : CompetitionSetup Student Subject) (sub : Subject) (current : Finset Student) :
    (computeTopHalf setup sub current).card = current.card / 2 := by
  classical
  unfold computeTopHalf
  simp only []
  set sorted := current.toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))
  have h_sorted_nodup : sorted.Nodup := by
    simpa [sorted] using
      (List.nodup_mergeSort (l := current.toList)
        (le := fun a b => decide (setup.score sub a ≥ setup.score sub b))).2
        (Finset.nodup_toList current)
  have h_take_nodup : (sorted.take (current.card / 2)).Nodup := by
    exact List.nodup_take_of_nodup h_sorted_nodup _
  rw [List.toFinset_card_of_nodup h_take_nodup]
  have h_len : sorted.length = current.card := by
    simpa [sorted] using
      (List.length_mergeSort (l := current.toList)
        (lt := fun a b => decide (setup.score sub a ≥ setup.score sub b)))
  have h_le : current.card / 2 ≤ current.card := Nat.div_le_self _ _
  rw [List.length_take]
  simp [h_len, h_le, Nat.min_eq_left]

lemma computeTopHalf_subset (setup : CompetitionSetup Student Subject) (sub : Subject) (current : Finset Student) :
    computeTopHalf setup sub current ⊆ current := by
  unfold computeTopHalf
  intro x hx
  simp only [List.mem_toFinset] at hx
  have : x ∈ current.toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b)) := by
    exact List.mem_of_mem_take hx
  have h_perm := List.mergeSort_perm current.toList (fun a b => decide (setup.score sub a ≥ setup.score sub b))
  have : x ∈ current.toList := (List.Perm.mem_iff h_perm).1 this
  exact Finset.mem_toList.mp this

lemma computeTopHalf_score_property (setup : CompetitionSetup Student Subject) (sub : Subject) (current : Finset Student) :
    ∀ x ∈ computeTopHalf setup sub current, ∀ y ∈ current \ computeTopHalf setup sub current,
      setup.score sub x ≥ setup.score sub y := by
  intro x hx y hy
  unfold computeTopHalf at hx hy
  simp only [Finset.mem_sdiff, List.mem_toFinset] at hx hy

  let sorted := current.toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))
  let k := current.card / 2

  -- x is in take k of sorted, y is in current but not in take k
  have hx_take : x ∈ sorted.take k := hx
  have hy_current : y ∈ current := hy.1
  have hy_not_take : y ∉ sorted.take k := hy.2

  -- The sorted list has pairwise ordering
  haveI : Std.Total (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
    ⟨by intro a b; exact le_total _ _⟩
  haveI : IsTrans Student (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
    ⟨by intro a b c hab hbc; exact le_trans hbc hab⟩
  have h_pairwise : sorted.Pairwise (fun a b => setup.score sub a ≥ setup.score sub b) := by
    simpa [sorted] using
      (List.pairwise_mergeSort' (r := fun a b => setup.score sub a ≥ setup.score sub b) current.toList)

  -- y is in the sorted list (since it's in current and sorted is a permutation)
  have hy_sorted : y ∈ sorted := by
    have h_perm := List.mergeSort_perm current.toList (fun a b => decide (setup.score sub a ≥ setup.score sub b))
    have : y ∈ current.toList := Finset.mem_toList.mpr hy_current
    exact (List.Perm.mem_iff h_perm.symm).1 this

  -- Get positions of x and y in the sorted list
  have hx_pos : ∃ (i : Nat) (hi : i < sorted.length), sorted[i] = x ∧ i < k := by
    rw [List.mem_iff_getElem] at hx_take
    obtain ⟨i, hi, hxi⟩ := hx_take
    use i
    have : i < sorted.length := by
      have h_len_le : (sorted.take k).length ≤ sorted.length := by
        simpa using (List.length_take_le (n := k) (l := sorted))
      exact lt_of_lt_of_le hi h_len_le
    use this
    constructor
    · rw [List.getElem_take] at hxi
      exact hxi
    · have : i < (sorted.take k).length := hi
      rw [List.length_take] at this
      omega

  have hy_pos : ∃ (j : Nat) (hj : j < sorted.length), sorted[j] = y := by
    rw [List.mem_iff_getElem] at hy_sorted
    exact hy_sorted

  obtain ⟨i, hi, hxi, hi_lt_k⟩ := hx_pos
  obtain ⟨j, hj, hyj⟩ := hy_pos

  -- If j < k, then y would be in take k, contradiction
  have hj_ge_k : j ≥ k := by
    by_contra h_not
    push_neg at h_not
    have : y ∈ sorted.take k := by
      rw [List.mem_iff_getElem]
      use j
      have : j < (sorted.take k).length := by
        rw [List.length_take]
        omega
      use this
      rw [List.getElem_take]
      exact hyj
    exact hy_not_take this

  -- Now use pairwise property: since i < j, score x > score y
  by_cases h_eq : i = j
  · -- If i = j, then x = y, so score x = score y
    subst h_eq
    have hxy : x = y := by
      simpa [hxi] using hyj
    simpa [hxy]
  · -- If i ≠ j, use pairwise property
    have hij : i < j ∨ j < i := Nat.lt_or_gt_of_ne h_eq
    cases hij with
    | inl hij =>
      -- i < j, so score x > score y by pairwise property
      have : setup.score sub (sorted[i]) ≥ setup.score sub (sorted[j]) := by
        have h_rel := List.pairwise_iff_get.mp h_pairwise
        exact h_rel ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hxy : setup.score sub x ≥ setup.score sub y := by
        simpa [hxi, hyj] using this
      exact hxy
    | inr hji =>
      -- j < i, but j ≥ k and i < k, contradiction
      omega

/-- 定义一个学生是否在特定的科目顺序下"存活到最后"。
    这里使用构造性定义以便于计算。-/
def Survives (setup : CompetitionSetup Student Subject) (ordering : List Subject) (x : Student) : Prop :=
  match ordering with
  | [s1, s2, s3] =>
      let S0 := (univ : Finset Student)
      let S1 := computeTopHalf setup s1 S0
      let S2 := computeTopHalf setup s2 S1
      let S3 := computeTopHalf setup s3 S2
      x ∈ S3
  | _ => False

/-- 获取所有潜在冠军的集合 -/
def getChampions (setup : CompetitionSetup Student Subject) : Finset Student :=
  let subjects := (univ : Finset Subject).toList
  let perms := permutations subjects
  -- 过滤出长度为3的排列（实际上所有全排列长度都为3，因为Subject card=3）
  let valid_perms := perms.filter (λ l => l.length = 3)
  let survivors := valid_perms.flatMap (λ p =>
    match p with
    | [s1, s2, s3] =>
        let S0 := (univ : Finset Student)
        let S1 := computeTopHalf setup s1 S0
        let S2 := computeTopHalf setup s2 S1
        let S3 := computeTopHalf setup s3 S2
        S3.toList
    | _ => [])
  survivors.toFinset

/-- 定义“潜在冠军”：在至少一种排列中存活 -/
def IsPotentialChampion (setup : CompetitionSetup Student Subject) (x : Student) : Prop :=
  x ∈ getChampions setup

/-- 计算潜在冠军的数量 -/
def countPotentialChampions (setup : CompetitionSetup Student Subject) : ℕ :=
  (getChampions setup).card

/-- 最终问题的形式化陈述 -/
def IsMaxPotentialChampions (N : ℕ) : Prop :=
  (∀ (Student Subject : Type*) [Fintype Student] [DecidableEq Student]
     [Fintype Subject] [DecidableEq Subject]
     (setup : CompetitionSetup Student Subject),
     countPotentialChampions setup ≤ N) ∧
  (∃ (Student Subject : Type*) (_ : Fintype Student) (_ : DecidableEq Student)
     (_ : Fintype Subject) (_ : DecidableEq Subject)
     (setup : CompetitionSetup Student Subject),
     countPotentialChampions setup = N)

/-- 构造一个具体的例子证明 N >= 5 -/
def exampleSetup : CompetitionSetup (Fin 8) (Fin 3) :=
  let score_fun : Fin 3 → Fin 8 → ℕ := fun sub stu =>
    match sub, stu with
    -- Subject 0 (A): Ranks 2, 3, 5, 1, 6, 4, 7, 8 -> Scores 7, 6, 4, 8, 3, 5, 2, 1
    | 0, 0 => 7 | 0, 1 => 6 | 0, 2 => 4 | 0, 3 => 8 | 0, 4 => 3 | 0, 5 => 5 | 0, 6 => 2 | 0, 7 => 1
    -- Subject 1 (B): Ranks 3, 4, 7, 8, 5, 6, 1, 2 -> Scores 6, 5, 2, 1, 4, 3, 8, 7
    | 1, 0 => 6 | 1, 1 => 5 | 1, 2 => 2 | 1, 3 => 1 | 1, 4 => 4 | 1, 5 => 3 | 1, 6 => 8 | 1, 7 => 7
    -- Subject 2 (C): Ranks 4, 1, 2, 6, 5, 3, 7, 8 -> Scores 5, 8, 7, 3, 4, 6, 2, 1
    | 2, 0 => 5 | 2, 1 => 8 | 2, 2 => 7 | 2, 3 => 3 | 2, 4 => 4 | 2, 5 => 6 | 2, 6 => 2 | 2, 7 => 1
  {
    student_count := by simp
    subject_count := by simp
    score := score_fun
    score_injective := by
      intro s a b h
      fin_cases s <;> fin_cases a <;> fin_cases b <;>
        simp [score_fun] at h <;>
        try cases h <;> rfl
  }

/-- 验证例子中的潜在冠军数为 5 -/
theorem example_count : countPotentialChampions exampleSetup = 5 := by
  classical
  native_decide

/-- 定义第一轮幸存者集合 S_X -/
def survivalSet (setup : CompetitionSetup Student Subject) (sub : Subject) : Finset Student :=
  computeTopHalf setup sub univ

/-- 引理：任意配置下，潜在冠军数不超过6 -/
lemma champions_le_six (setup : CompetitionSetup Student Subject) :
    countPotentialChampions setup ≤ 6 := by
  classical
  -- 最多有 3! = 6 种排列
  unfold countPotentialChampions getChampions
  set subjects := (univ : Finset Subject).toList
  set perms := subjects.permutations
  set valid_perms := perms.filter (fun l => decide (l.length = 3))
  set f : List Subject → List Student := fun p =>
    match p with
    | [s1, s2, s3] =>
        let S0 := (univ : Finset Student)
        let S1 := computeTopHalf setup s1 S0
        let S2 := computeTopHalf setup s2 S1
        let S3 := computeTopHalf setup s3 S2
        S3.toList
    | _ => []
  set survivors := valid_perms.flatMap f
  have h_card : valid_perms.length ≤ 6 := by
    have h1 : (univ : Finset Subject).toList.length = 3 := by
      simpa [Finset.length_toList, setup.subject_count]
    have h2 : perms.length = Nat.factorial 3 := by
      rw [List.length_permutations, h1]
    have h3 : valid_perms.length ≤ perms.length := by
      exact List.length_filter_le _ _
    rw [h2] at h3
    norm_num at h3
    exact h3
  have h_winner_len : ∀ s1 s2 s3,
      let S0 := (univ : Finset Student)
      let S1 := computeTopHalf setup s1 S0
      let S2 := computeTopHalf setup s2 S1
      let S3 := computeTopHalf setup s3 S2
      S3.toList.length = 1 := by
    intro s1 s2 s3
    have hS1 : (computeTopHalf setup s1 (univ : Finset Student)).card = 4 := by
      simpa [Finset.card_univ, setup.student_count] using
        (computeTopHalf_card setup s1 (univ : Finset Student))
    have hS2 : (computeTopHalf setup s2 (computeTopHalf setup s1 (univ : Finset Student))).card = 2 := by
      simpa [hS1] using
        (computeTopHalf_card setup s2 (computeTopHalf setup s1 (univ : Finset Student)))
    have hS3 : (computeTopHalf setup s3
        (computeTopHalf setup s2 (computeTopHalf setup s1 (univ : Finset Student)))).card = 1 := by
      simpa [hS2] using
        (computeTopHalf_card setup s3
          (computeTopHalf setup s2 (computeTopHalf setup s1 (univ : Finset Student))))
    simpa [Finset.length_toList] using hS3
  have h_len_each : ∀ p ∈ valid_perms, (f p).length ≤ 1 := by
    intro p hp
    have hp' : p ∈ perms.filter (fun l => decide (l.length = 3)) := by
      simpa [valid_perms] using hp
    have hp_len : p.length = 3 := by
      have : decide (p.length = 3) = true := (List.mem_filter.mp hp').2
      simpa using this
    cases p with
    | nil => cases hp_len
    | cons a t =>
      cases t with
      | nil => cases hp_len
      | cons b t2 =>
        cases t2 with
        | nil => cases hp_len
        | cons c t3 =>
          cases t3 with
          | nil =>
            simp [f, h_winner_len]
          | cons _ _ => cases hp_len
  have h_survivors_len : survivors.length ≤ valid_perms.length := by
    have h_general :
        ∀ l : List (List Subject), (∀ p ∈ l, (f p).length ≤ 1) →
          (l.flatMap f).length ≤ l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons p ps ih =>
        have hp : (f p).length ≤ 1 := hl p (by simp)
        have hps : ∀ q ∈ ps, (f q).length ≤ 1 := by
          intro q hq
          exact hl q (by simp [hq])
        simpa [List.flatMap, List.length, List.length_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (add_le_add hp (ih hps))
    exact h_general valid_perms h_len_each
  have h_card_survivors : (List.toFinset survivors).card ≤ survivors.length := by
    simpa using (List.toFinset_card_le (l := survivors))
  calc
      (List.toFinset survivors).card
          ≤ survivors.length := h_card_survivors
      _ ≤ valid_perms.length := h_survivors_len
      _ ≤ 6 := h_card

/-- 辅助引理：如果所有交集大小都≤1，则交集和≤3 -/
lemma intersection_sum_le_three_of_all_le_one
    {U : Type*} [Fintype U] [DecidableEq U]
    (S1 S2 S3 : Finset U)
    (h1 : (S1 ∩ S2).card ≤ 1)
    (h2 : (S2 ∩ S3).card ≤ 1)
    (h3 : (S3 ∩ S1).card ≤ 1) :
    (S1 ∩ S2).card + (S2 ∩ S3).card + (S3 ∩ S1).card ≤ 3 := by
  omega

/-- 辅助引理：如果交集和≥4，则至少存在一个交集大小≥2 -/
lemma exists_intersection_ge_two_of_sum_ge_four
    {U : Type*} [Fintype U] [DecidableEq U]
    (S1 S2 S3 : Finset U)
    (h : (S1 ∩ S2).card + (S2 ∩ S3).card + (S3 ∩ S1).card ≥ 4) :
    (S1 ∩ S2).card ≥ 2 ∨ (S2 ∩ S3).card ≥ 2 ∨ (S3 ∩ S1).card ≥ 2 := by
  by_contra h_not
  push_neg at h_not
  have h1 : (S1 ∩ S2).card ≤ 1 := by omega
  have h2 : (S2 ∩ S3).card ≤ 1 := by omega
  have h3 : (S3 ∩ S1).card ≤ 1 := by omega
  have : (S1 ∩ S2).card + (S2 ∩ S3).card + (S3 ∩ S1).card ≤ 3 :=
    intersection_sum_le_three_of_all_le_one S1 S2 S3 h1 h2 h3
  omega

/-- 辅助引理：交集大小的上界 -/
lemma inter_card_le_min {U : Type*} [DecidableEq U] (S1 S2 : Finset U) :
    (S1 ∩ S2).card ≤ min S1.card S2.card := by
  have : S1 ∩ S2 ⊆ S1 := Finset.inter_subset_left
  have h1 : (S1 ∩ S2).card ≤ S1.card := Finset.card_le_card this
  have : S1 ∩ S2 ⊆ S2 := Finset.inter_subset_right
  have h2 : (S1 ∩ S2).card ≤ S2.card := Finset.card_le_card this
  omega

/-- 辅助引理：交集大小的对称性 -/
lemma inter_card_comm {U : Type*} [DecidableEq U] (S1 S2 : Finset U) :
    (S1 ∩ S2).card = (S2 ∩ S1).card := by
  congr 1
  ext x
  simp [Finset.mem_inter, and_comm]

/-- 辅助引理：如果交集大小≥2，则交集非空 -/
lemma inter_nonempty_of_card_ge_two {U : Type*} [DecidableEq U] (S1 S2 : Finset U)
    (h : (S1 ∩ S2).card ≥ 2) :
    (S1 ∩ S2).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h_empty
  rw [h_empty] at h
  simp at h

/-- 辅助引理：空集的基数为0 -/
lemma card_empty_eq_zero {U : Type*} : (∅ : Finset U).card = 0 := Finset.card_empty

/-- 辅助引理：单元素集合的基数为1 -/
lemma card_singleton_eq_one {U : Type*} (x : U) : ({x} : Finset U).card = 1 := Finset.card_singleton x

/-- 辅助引理：两元素集合的基数为2（如果元素不同） -/
lemma card_pair_eq_two {U : Type*} [DecidableEq U] (x y : U) (h : x ≠ y) :
    ({x, y} : Finset U).card = 2 := by
  classical
  have hx : x ∉ ({y} : Finset U) := by
    simp [h]
  simpa [Finset.card_singleton] using
    (Finset.card_insert_of_notMem (s := {y}) (a := x) hx)

/-- 辅助引理：三元素集合的基数为3（如果元素互不相同） -/
lemma card_triple_eq_three {U : Type*} [DecidableEq U] (x y z : U)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Finset U).card = 3 := by
  classical
  have h_yz : ({y, z} : Finset U).card = 2 := card_pair_eq_two y z hyz
  have hx : x ∉ ({y, z} : Finset U) := by
    simp [hxy, hxz]
  simpa [h_yz, Finset.insert_comm] using
    (Finset.card_insert_of_notMem (s := {y, z}) (a := x) hx)

/-- 辅助引理：如果S1 ⊆ S2且基数相等，则S1 = S2 -/
lemma eq_of_subset_of_card_eq {U : Type*} [DecidableEq U] (S1 S2 : Finset U)
    (h_sub : S1 ⊆ S2) (h_card : S1.card = S2.card) :
    S1 = S2 := by
  apply Finset.eq_of_subset_of_card_le h_sub
  omega

/-- 辅助引理：并集的基数上界 -/
lemma card_union_le {U : Type*} [DecidableEq U] (S1 S2 : Finset U) :
    (S1 ∪ S2).card ≤ S1.card + S2.card := Finset.card_union_le S1 S2

lemma mem_of_mem_drop {α : Type*} {a : α} {l : List α} {n : Nat} :
    a ∈ l.drop n → a ∈ l := by
  induction n generalizing l with
  | zero =>
      intro h
      simpa using h
  | succ n ih =>
      intro h
      cases l with
      | nil =>
          simpa using h
      | cons b l =>
          simp at h
          exact List.mem_cons_of_mem _ (ih h)

lemma getElem?_take_of_lt' {α : Type*} (l : List α) {n i : Nat} (h : i < n) :
    (l.take n)[i]? = l[i]? := by
  induction l generalizing n i with
  | nil =>
      simp
  | cons a l ih =>
      cases n with
      | zero =>
          cases h
      | succ n =>
          cases i with
          | zero =>
              simp
          | succ i =>
              simp at h
              simp [ih h]

-- (card_pair_eq_two moved above)

/-- 辅助引理：幸存者集合的大小为4 -/
lemma survivalSet_card (setup : CompetitionSetup Student Subject) (sub : Subject) :
    (survivalSet setup sub).card = 4 := by
  unfold survivalSet computeTopHalf
  -- 需要证明：
  -- 1. univ.card = 8（由setup.student_count）
  -- 2. univ.card / 2 = 4
  -- 3. take 4会选中4个元素（如果列表长度≥4）
  -- 4. toFinset保持基数
  have h_univ_card : (univ : Finset Student).card = 8 := setup.student_count
  have h_list_len : (univ : Finset Student).toList.length = 8 := by
    rw [Finset.length_toList, h_univ_card]
  have h_sorted_len : ((univ : Finset Student).toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))).length = 8 := by
    rw [List.length_mergeSort, h_list_len]
  have h_take_len : (((univ : Finset Student).toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))).take ((univ : Finset Student).card / 2)).length = 4 := by
    rw [List.length_take, h_sorted_len, h_univ_card]
    norm_num
  -- Now we need to show that toFinset preserves the cardinality
  -- This requires showing the list has no duplicates
  have h_nodup : (((univ : Finset Student).toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))).take ((univ : Finset Student).card / 2)).Nodup := by
    apply List.nodup_take_of_nodup
    have h_perm := List.mergeSort_perm (univ : Finset Student).toList (fun a b => decide (setup.score sub a ≥ setup.score sub b))
    exact (List.Perm.nodup_iff h_perm).mpr (Finset.nodup_toList univ)
  rw [List.toFinset_card_of_nodup h_nodup, h_take_len]

/-- 辅助引理：幸存者集合是univ的子集 -/
lemma survivalSet_subset_univ (setup : CompetitionSetup Student Subject) (sub : Subject) :
    survivalSet setup sub ⊆ univ := by
  apply Finset.subset_univ

/-- 辅助引理：从基数为3的有限类型中提取三个不同元素 -/
lemma exists_three_distinct_of_card_eq_three
    {α : Type*} [Fintype α] [DecidableEq α] (h : Fintype.card α = 3) :
    ∃ (a b c : α), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ (univ : Finset α) = {a, b, c} := by
  have : (univ : Finset α).card = 3 := by
    rw [Finset.card_univ, h]
  rw [Finset.card_eq_three] at this
  obtain ⟨a, b, c, hab, hac, hbc, huniv⟩ := this
  exact ⟨a, b, c, hab, hbc, hac, huniv⟩

/-- 辅助引理：如果两个大小为4的集合的交集大小为4，则它们相等 -/
lemma eq_of_inter_card_eq_four {U : Type*} [DecidableEq U] (S1 S2 : Finset U)
    (h1 : S1.card = 4) (h2 : S2.card = 4) (h_inter : (S1 ∩ S2).card = 4) :
    S1 = S2 := by
  have h_eq1 : S1 ∩ S2 = S1 := by
    apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_left : S1 ∩ S2 ⊆ S1)
    simpa [h_inter, h1]
  have h_eq2 : S1 ∩ S2 = S2 := by
    apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_right : S1 ∩ S2 ⊆ S2)
    simpa [h_inter, h2]
  rw [← h_eq1, h_eq2]

/-- 辅助引理：Finset的交集是可交换的 -/
lemma inter_comm_card {U : Type*} [DecidableEq U] (S1 S2 : Finset U) :
    (S1 ∩ S2).card = (S2 ∩ S1).card := by
  congr 1
  ext x
  simp [Finset.mem_inter]
  tauto

/-- 辅助定义：在给定科目上的排名 -/
def rank (setup : CompetitionSetup Student Subject) (sub : Subject) (s : Student) : ℕ :=
  (univ.filter (fun t => setup.score sub t > setup.score sub s)).card + 1

/-- 辅助引理：mergeSort后的列表包含原列表的所有元素 -/
lemma mem_mergeSort_iff {α : Type*} [DecidableEq α] (r : α → α → Bool) (l : List α) (x : α) :
    x ∈ l.mergeSort r ↔ x ∈ l := by
  have h := List.mergeSort_perm l r
  exact List.Perm.mem_iff h

/-- 辅助引理：排名≤4等价于在幸存者集合中 -/
lemma rank_le_four_iff_in_survival (setup : CompetitionSetup Student Subject) (sub : Subject) (s : Student) :
    rank setup sub s ≤ 4 ↔ s ∈ survivalSet setup sub := by
  unfold rank survivalSet computeTopHalf
  constructor
  · intro h_rank
    -- 排名≤4意味着至多3个学生分数更高
    have h_count : (univ.filter (fun t => setup.score sub t > setup.score sub s)).card ≤ 3 := by omega
    -- s必在排序后的前4个位置
    have h_univ_card : (univ : Finset Student).card = 8 := setup.student_count
    have hk : (univ : Finset Student).card / 2 = 4 := by
      simpa [h_univ_card]
    have hk' : (Fintype.card Student) / 2 = 4 := by
      simpa [setup.student_count]
    have h_s_in_univ : s ∈ (univ : Finset Student) := Finset.mem_univ s

    -- 排序后的列表
    let sorted := (univ : Finset Student).toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))

    -- s在原列表中
    have h_s_in_list : s ∈ (univ : Finset Student).toList := by
      rw [Finset.mem_toList]
      exact h_s_in_univ

    -- s在排序后的列表中
    have h_s_in_sorted : s ∈ sorted := by
      rw [mem_mergeSort_iff]
      exact h_s_in_list

    -- 关键：如果至多3个学生分数更高，则s在前4个位置
    -- 使用反证法
    by_contra h_not_in_take

    -- s不在take 4中，意味着s在drop 4中
    have h_s_in_drop : s ∈ sorted.drop 4 := by
      have h_sorted_eq : sorted.take 4 ++ sorted.drop 4 = sorted := List.take_append_drop 4 sorted
      have : s ∈ sorted.take 4 ∨ s ∈ sorted.drop 4 := by
        rw [← h_sorted_eq] at h_s_in_sorted
        exact List.mem_append.mp h_s_in_sorted
      cases this with
      | inl h =>
        have h' : s ∈ (sorted.take (Fintype.card Student / 2)).toFinset := by
          simpa [hk'] using (List.mem_toFinset.mpr h)
        exact (h_not_in_take h').elim
      | inr h => exact h

    -- 排序后的列表是按分数降序排列的
    haveI : Std.Total (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
      ⟨by intro a b; exact le_total _ _⟩
    haveI : IsTrans Student (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
      ⟨by intro a b c hab hbc; exact le_trans hbc hab⟩
    have h_pairwise : sorted.Pairwise (fun a b => setup.score sub a ≥ setup.score sub b) := by
      simpa [sorted] using
        (List.pairwise_mergeSort' (r := fun a b => setup.score sub a ≥ setup.score sub b)
          (univ : Finset Student).toList)

    -- 前4个位置的学生分数都比s高
    -- 但这与"至多3个学生分数更高"矛盾
    have h_take_len : (sorted.take 4).length = 4 := by
      rw [List.length_take]
      have : sorted.length = 8 := by
        rw [List.length_mergeSort]
        have h_univ_len :
            (univ : Finset Student).toList.length = (univ : Finset Student).card := by
          simpa using (Finset.length_toList (s := (univ : Finset Student)))
        exact h_univ_len ▸ h_univ_card
      rw [this]
      norm_num

    -- 前4个位置有4个不同的学生
    have h_take_nodup : (sorted.take 4).Nodup := by
      apply List.nodup_take_of_nodup
      have h_perm := List.mergeSort_perm (univ : Finset Student).toList (fun a b => decide (setup.score sub a ≥ setup.score sub b))
      exact (List.Perm.nodup_iff h_perm).mpr (Finset.nodup_toList univ)

    -- 这4个学生都比s分数高
    have h_all_greater : ∀ t ∈ sorted.take 4, setup.score sub t > setup.score sub s := by
      intro t ht
      have ht_fin : t ∈ computeTopHalf setup sub (univ : Finset Student) := by
        unfold computeTopHalf
        simpa [hk'] using (List.mem_toFinset.mpr ht)
      have hs_not :
          s ∈ (univ : Finset Student) \ computeTopHalf setup sub (univ : Finset Student) := by
        refine Finset.mem_sdiff.mpr ?_
        refine ⟨Finset.mem_univ s, ?_⟩
        -- `h_not_in_take` is the negation of membership in `computeTopHalf`
        simpa [computeTopHalf, hk'] using h_not_in_take
      have h_le_score :
          setup.score sub t ≥ setup.score sub s :=
        computeTopHalf_score_property setup sub (univ : Finset Student) t ht_fin s hs_not
      have h_ne : t ≠ s := by
        intro h_eq
        subst h_eq
        exact (Finset.mem_sdiff.mp hs_not).2 ht_fin
      have h_ne_score : setup.score sub s ≠ setup.score sub t := by
        intro h_eq
        apply h_ne
        exact (setup.score_injective sub h_eq).symm
      have h_lt : setup.score sub s < setup.score sub t := by
        have h_le' : setup.score sub s ≤ setup.score sub t := by
          simpa [ge_iff_le] using h_le_score
        exact lt_of_le_of_ne h_le' h_ne_score
      exact h_lt

    -- 因此至少有4个学生分数更高
    have h_at_least_4 : (univ.filter (fun t => setup.score sub t > setup.score sub s)).card ≥ 4 := by
      have : (sorted.take 4).toFinset ⊆ univ.filter (fun t => setup.score sub t > setup.score sub s) := by
        intro t ht
        rw [List.mem_toFinset] at ht
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ t
        · exact h_all_greater t ht
      calc (univ.filter (fun t => setup.score sub t > setup.score sub s)).card
          ≥ (sorted.take 4).toFinset.card := by
              simpa [ge_iff_le] using (Finset.card_le_card this)
        _ = (sorted.take 4).length := by
              rw [List.toFinset_card_of_nodup h_take_nodup]
        _ = 4 := h_take_len

    -- 矛盾
    omega

  · intro h_in_survival
    have h_top : s ∈ computeTopHalf setup sub (univ : Finset Student) := by
      dsimp [survivalSet] at h_in_survival
      exact h_in_survival
    have h_top_card : (computeTopHalf setup sub (univ : Finset Student)).card = 4 := by
      simpa [survivalSet] using survivalSet_card setup sub
    have h_sub :
        (univ.filter (fun t => setup.score sub t > setup.score sub s)) ⊆
          computeTopHalf setup sub (univ : Finset Student) := by
      intro t ht
      have ht_univ : t ∈ (univ : Finset Student) := (Finset.mem_filter.mp ht).1
      have ht_gt : setup.score sub t > setup.score sub s := (Finset.mem_filter.mp ht).2
      by_contra ht_not
      have ht_not' :
          t ∈ (univ : Finset Student) \ computeTopHalf setup sub (univ : Finset Student) :=
        Finset.mem_sdiff.mpr ⟨ht_univ, ht_not⟩
      have h_le :
          setup.score sub s ≥ setup.score sub t :=
        computeTopHalf_score_property setup sub (univ : Finset Student) s h_top t ht_not'
      exact (not_le_of_gt ht_gt) h_le
    have h_not_mem : s ∉ (univ.filter (fun t => setup.score sub t > setup.score sub s)) := by
      simp
    have h_card_le : (univ.filter (fun t => setup.score sub t > setup.score sub s)).card ≤ 4 := by
      simpa [h_top_card] using (Finset.card_le_card h_sub)
    have h_card_ne : (univ.filter (fun t => setup.score sub t > setup.score sub s)).card ≠ 4 := by
      intro h_eq
      have h_eq_sets :
          (univ.filter (fun t => setup.score sub t > setup.score sub s)) =
            computeTopHalf setup sub (univ : Finset Student) := by
        apply Finset.eq_of_subset_of_card_le h_sub
        simpa [h_eq, h_top_card]
      have : s ∈ (univ.filter (fun t => setup.score sub t > setup.score sub s)) := by
        simpa [h_eq_sets] using h_top
      exact h_not_mem this
    have h_card_le3 : (univ.filter (fun t => setup.score sub t > setup.score sub s)).card ≤ 3 := by
      have h_lt4 :
          (univ.filter (fun t => setup.score sub t > setup.score sub s)).card < 4 :=
        lt_of_le_of_ne h_card_le h_card_ne
      exact Nat.le_of_lt_succ h_lt4
    omega
  /-
    -- s在take 4的toFinset中
    rw [List.mem_toFinset] at h_in_survival

    -- 排序后的列表
    let sorted := (univ : Finset Student).toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))

    -- 排序后的列表是按分数降序排列的
    have h_pairwise : sorted.Pairwise (fun a b => setup.score sub a > setup.score sub b) := by
      simpa [sorted] using
        (List.pairwise_mergeSort' (r := fun a b => setup.score sub a > setup.score sub b)
          (univ : Finset Student).toList)

    -- s在前4个位置
    -- 因此至多3个学生分数更高（即前面的位置）
    have h_take_len : (sorted.take 4).length = 4 := by
      rw [List.length_take]
      have : sorted.length = 8 := by
        rw [List.length_mergeSort]
        have : (univ : Finset Student).toList.length = 8 := by
          rw [Finset.length_toList, setup.student_count]
        exact this
      rw [this]
      norm_num

    -- s在take 4中的索引
    have h_s_idx : ∃ i, i < 4 ∧ sorted.take 4[i]? = some s := by
      have : s ∈ sorted.take 4 := h_in_survival
      obtain ⟨i, hi, hs⟩ := List.mem_iff_getElem.mp this
      use i
      constructor
      · calc i < sorted.take 4.length := hi
          _ = 4 := h_take_len
      · rw [List.getElem?_eq_getElem hi]
        simp [hs]

    -- 至多i个学生分数更高（i < 4）
    obtain ⟨i, hi, hs_at_i⟩ := h_s_idx

    -- 分数更高的学生只能在前i个位置
    have h_greater_in_prefix : ∀ t ∈ univ, setup.score sub t > setup.score sub s →
        ∃ j, j < i ∧ sorted.take 4[j]? = some t := by
      intro t ht_univ ht_greater
      -- t必在sorted中
      have ht_in_sorted : t ∈ sorted := by
        rw [mem_mergeSort_iff]
        rw [Finset.mem_toList]
        exact ht_univ
      -- 如果t在take 4中
      by_cases ht_in_take : t ∈ sorted.take 4
      · -- t在take 4中的某个位置j
        obtain ⟨j, hj, ht_at_j⟩ := List.mem_iff_getElem.mp ht_in_take
        use j
        constructor
        · -- 需要证明j < i
          -- 因为t分数更高，且列表按降序排列
          by_contra h_not_lt
          push_neg at h_not_lt
          -- j ≥ i
          have : i ≤ j := h_not_lt
          -- 但这意味着sorted[i] ≥ sorted[j]（按分数）
          -- 即s的分数 ≥ t的分数
          have h_s_at_i_full : sorted.take 4[i] = s := by
            have : sorted.take 4[i]? = some s := hs_at_i
            cases h_eq : sorted.take 4[i]?
            · simp at this
            · simp at this
              rw [h_eq] at this
              simp at this
              exact this
          have h_t_at_j_full : sorted.take 4[j] = t := ht_at_j
          -- 使用pairwise性质
          have h_take_pairwise : (sorted.take 4).Pairwise (fun a b => setup.score sub a > setup.score sub b) := by
            exact List.Pairwise.take _ h_pairwise
          have : setup.score sub (sorted.take 4[i]) > setup.score sub (sorted.take 4[j]) := by
            apply List.Pairwise.rel_get_of_lt h_take_pairwise
            constructor
            · exact hi
            · calc i < j := by omega
                _ < sorted.take 4.length := hj
          rw [h_s_at_i_full, h_t_at_j_full] at this
          -- 矛盾：s分数 > t分数，但我们假设t分数 > s分数
          omega
        · rw [List.getElem?_eq_getElem hj]
          simp [ht_at_j]
      · -- t不在take 4中，则t在drop 4中
        have ht_in_drop : t ∈ sorted.drop 4 := by
          have h_sorted_eq : sorted = sorted.take 4 ++ sorted.drop 4 := List.take_append_drop 4 sorted
          have : t ∈ sorted.take 4 ∨ t ∈ sorted.drop 4 := by
            rw [←h_sorted_eq] at ht_in_sorted
            exact List.mem_append.mp ht_in_sorted
          cases this with
          | inl h => contradiction
          | inr h => exact h
        -- 但s在take 4中，t在drop 4中
        -- 由pairwise性质，s分数 > t分数
        have : setup.score sub s > setup.score sub t := by
          exact List.Pairwise.rel_of_mem_take_of_mem_drop h_pairwise h_in_survival ht_in_drop
        -- 矛盾
        omega

    -- 因此分数更高的学生数量≤ i < 4
    have : (univ.filter (fun t => setup.score sub t > setup.score sub s)).card ≤ i := by
      -- 每个分数更高的学生对应前i个位置中的一个
      -- 由于前i个位置至多有i个学生，所以分数更高的学生至多i个
      have h_take_i_nodup : (sorted.take 4.take i).Nodup := by
        apply List.nodup_take_of_nodup
        apply List.nodup_take_of_nodup
        have h_perm := List.mergeSort_perm (univ : Finset Student).toList (fun a b => setup.score sub a > setup.score sub b)
        exact List.Perm.nodup_iff h_perm |>.mpr (Finset.nodup_toList univ)
      have h_take_i_len : (sorted.take 4.take i).length = i := by
        rw [List.length_take]
        rw [h_take_len]
        simp [hi]
      have : univ.filter (fun t => setup.score sub t > setup.score sub s) ⊆ (sorted.take 4.take i).toFinset := by
        intro t ht
        rw [Finset.mem_filter] at ht
        obtain ⟨j, hj, ht_at_j⟩ := h_greater_in_prefix t ht.1 ht.2
        rw [List.mem_toFinset]
        have : j < (sorted.take 4.take i).length := by
          rw [h_take_i_len]
          exact hj
        have : sorted.take 4.take i[j]? = some t := by
          rw [List.getElem?_take]
          have : j < sorted.take 4.length := by
            calc j < i := hj
              _ < 4 := hi
              _ = sorted.take 4.length := h_take_len.symm
          rw [List.getElem?_eq_getElem this]
          simp
          cases h_eq : sorted.take 4[j]?
          · rw [h_eq] at ht_at_j
            simp at ht_at_j
          · rw [h_eq] at ht_at_j
            simp at ht_at_j
            rw [←ht_at_j]
            have : sorted.take 4[j]? = some (sorted.take 4[j]) := by
              rw [List.getElem?_eq_getElem this]
              simp
            rw [h_eq] at this
            simp at this
            exact this.symm
        exact List.mem_of_getElem?_eq_some this
      calc (univ.filter (fun t => setup.score sub t > setup.score sub s)).card
          ≤ (sorted.take 4.take i).toFinset.card := Finset.card_le_card this
        _ = (sorted.take 4.take i).length := by rw [List.toFinset_card_of_nodup h_take_i_nodup]
        _ = i := h_take_i_len

    -- 因此排名 = 分数更高的学生数 + 1 ≤ i + 1 ≤ 4
    calc rank setup sub s
        = (univ.filter (fun t => setup.score sub t > setup.score sub s)).card + 1 := rfl
      _ ≤ i + 1 := by omega
      _ ≤ 4 := by omega
  -/

/-- 辅助引理：如果学生在S_Y中，则其Y排名≤4 -/
lemma in_survival_implies_rank_le_four (setup : CompetitionSetup Student Subject) (sub : Subject) (s : Student) :
    s ∈ survivalSet setup sub → rank setup sub s ≤ 4 := by
  intro h
  exact (rank_le_four_iff_in_survival setup sub s).2 h

/-- 辅助引理：如果学生不在S_Y中，则其Y排名>4 -/
lemma not_in_survival_implies_rank_gt_four (setup : CompetitionSetup Student Subject) (sub : Subject) (s : Student) :
    s ∉ survivalSet setup sub → rank setup sub s > 4 := by
  intro h
  by_contra h_not_gt
  push_neg at h_not_gt
  have : s ∈ survivalSet setup sub :=
    (rank_le_four_iff_in_survival setup sub s).1 h_not_gt
  contradiction

/-- 辅助引理：计算排列中某个子集在列表中的元素数量 -/
lemma count_subset_in_perm {α : Type*} [DecidableEq α] [Fintype α]
    (s t : Finset α) (l : List α) (k : ℕ)
    (ht_sub : t ⊆ s) (ht_card : t.card = k) (h_perm : l.Perm s.toList) :
    (l.filter (fun x => x ∈ t)).length = k := by
  classical
  have h_nodup_l : l.Nodup := (List.Perm.nodup_iff h_perm).2 (Finset.nodup_toList s)
  have h_nodup_filter : (l.filter (fun x => x ∈ t)).Nodup :=
    List.Nodup.filter _ h_nodup_l
  have h_len :
      (l.filter (fun x => x ∈ t)).toFinset.card =
        (l.filter (fun x => x ∈ t)).length := by
    simpa using (List.toFinset_card_of_nodup h_nodup_filter)
  have h_finset :
      (l.filter (fun x => x ∈ t)).toFinset =
        l.toFinset.filter (fun x => decide (x ∈ t)) := by
    simpa using (List.toFinset_filter l (fun x => decide (x ∈ t)))
  have h_finset' :
      l.toFinset.filter (fun x => decide (x ∈ t)) = l.toFinset ∩ t := by
    ext x
    simp [Finset.mem_filter, Finset.mem_inter]
  have h_l_eq_s : l.toFinset = s := by
    ext x
    constructor
    · intro hx
      have hx_l : x ∈ l := by
        simpa [List.mem_toFinset] using hx
      have hx_slist : x ∈ s.toList := (List.Perm.mem_iff h_perm).1 hx_l
      simpa [Finset.mem_toList] using hx_slist
    · intro hx
      have hx_slist : x ∈ s.toList := by
        simpa [Finset.mem_toList] using hx
      have hx_l : x ∈ l := (List.Perm.mem_iff h_perm).2 hx_slist
      simpa [List.mem_toFinset] using hx_l
  calc
    (l.filter (fun x => x ∈ t)).length
        = (l.filter (fun x => x ∈ t)).toFinset.card := h_len.symm
    _ = (l.toFinset.filter (fun x => decide (x ∈ t))).card := by
        rw [h_finset]
    _ = (l.toFinset ∩ t).card := by
        rw [h_finset']
    _ = (s ∩ t).card := by simpa [h_l_eq_s]
    _ = t.card := by
        simpa [Finset.inter_eq_right.mpr ht_sub]
    _ = k := ht_card

/-- 关键引理：如果我们按分数对finset排序（降序），且子集t的所有元素分数
    都高于s\t的所有元素，则前|t|个元素恰好是t -/
lemma top_k_equals_high_score_subset {α : Type*} [DecidableEq α] [Fintype α]
    (s : Finset α) (t : Finset α) (score : α → ℕ) (k : ℕ)
    (ht_sub : t ⊆ s)
    (ht_card : t.card = k)
    (hs_card : k ≤ s.card)
    (h_scores : ∀ x ∈ t, ∀ y ∈ s \ t, score x > score y) :
    let sorted := s.toList.mergeSort (fun a b => decide (score a ≥ score b))
    (sorted.take k).toFinset = t := by
  intro sorted

  -- Key facts about sorted
  have h_perm : sorted.Perm s.toList :=
    List.mergeSort_perm s.toList (fun a b => decide (score a ≥ score b))
  haveI : Std.Total (fun a b : α => score a ≥ score b) :=
    ⟨by intro a b; exact le_total _ _⟩
  haveI : IsTrans α (fun a b : α => score a ≥ score b) :=
    ⟨by intro a b c hab hbc; exact le_trans hbc hab⟩
  have h_sorted : sorted.Pairwise (fun a b => score a ≥ score b) := by
    simpa [sorted] using
      (List.pairwise_mergeSort' (r := fun a b => score a ≥ score b) s.toList)
  have h_nodup : sorted.Nodup := by
    rw [List.nodup_iff_perm_nodup h_perm]
    exact Finset.nodup_toList s
  have h_length : sorted.length = s.card := by
    simpa [sorted] using
      (List.length_mergeSort (l := s.toList) (lt := fun a b => decide (score a > score b)))

  -- Strategy: Show that the first k elements of sorted are exactly the elements of t
  ext x
  constructor
  · -- If x ∈ (sorted.take k).toFinset, then x ∈ t
    intro hx
    by_contra hx_not_t
    -- x is in the first k positions but not in t, so x ∈ s\t
    have hx_in_s : x ∈ s := by
      have : x ∈ sorted := by
        rw [List.mem_toFinset] at hx
        exact List.mem_of_mem_take hx
      have : x ∈ s.toList := (List.Perm.mem_iff h_perm).1 this
      exact Finset.mem_toList.mp this
    have hx_in_sdiff : x ∈ s \ t := Finset.mem_sdiff.mpr ⟨hx_in_s, hx_not_t⟩

    -- Find position of x in sorted
    rw [List.mem_toFinset, List.mem_take] at hx
    obtain ⟨i, hi_lt_k, hi_lt, hxi⟩ := hx
    have hxi' : sorted[i] = x := by
      simpa using hxi

    -- Count elements of t in positions < i
    let t_before_i := (sorted.take i).toFinset ∩ t
    have h_t_before_card : t_before_i.card ≤ i := by
      calc t_before_i.card
          ≤ (sorted.take i).toFinset.card := Finset.card_inter_le _ _
        _ ≤ (sorted.take i).length := by
            rw [List.toFinset_card_of_nodup]
            exact List.nodup_take_of_nodup h_nodup i
        _ = min i sorted.length := by
            simpa using (List.length_take (l := sorted) (n := i))
        _ ≤ i := Nat.min_le_left _ _

    -- Since t.card = k and only ≤ i elements of t are before position i,
    -- at least k - i elements of t must be at positions ≥ i
    have h_t_after : k - i ≤ (t \ t_before_i).card := by
      have h_sub : t_before_i ⊆ t := by
        intro y hy
        simp [t_before_i, Finset.mem_inter] at hy
        exact hy.2
      have h_partition : t_before_i.card + (t \ t_before_i).card = t.card := by
        have h_diff : (t \ t_before_i).card = t.card - t_before_i.card := by
          simpa using (Finset.card_sdiff_of_subset h_sub)
        have h_le : t_before_i.card ≤ t.card := Finset.card_le_card h_sub
        calc
          t_before_i.card + (t \ t_before_i).card
              = t_before_i.card + (t.card - t_before_i.card) := by simpa [h_diff]
          _ = (t.card - t_before_i.card) + t_before_i.card := by
              simp [Nat.add_comm]
          _ = t.card := by
              exact Nat.sub_add_cancel h_le
      have h_diff : (t \ t_before_i).card = k - t_before_i.card := by
        -- 用 t.card = k
        have hk : t.card = k := by simpa [ht_card]
        -- 从 h_partition 推出
        have := congrArg (fun n => n - t_before_i.card) h_partition
        -- t_before_i.card + diff - t_before_i.card = t.card - t_before_i.card
        simp [Nat.add_sub_cancel_left, hk] at this
        exact this
      -- 由 t_before_i.card ≤ i 得到 k - i ≤ k - t_before_i.card
      have h_le : t_before_i.card ≤ i := h_t_before_card
      have h_sub_le : k - i ≤ k - t_before_i.card := Nat.sub_le_sub_left h_le _
      -- 代入 h_diff
      exact h_diff ▸ h_sub_le

    -- Since k - i ≥ 1 (because i < k), there exists at least one element of t at position ≥ i
    have : k - i ≥ 1 := by
      have : i < k := hi_lt_k
      exact Nat.succ_le_iff.mp (Nat.sub_pos_of_lt this)
    have h_exists_t_after_i :
        ∃ y ∈ t, ∃ j, i ≤ j ∧ ∃ hj_lt : j < sorted.length, sorted.get ⟨j, hj_lt⟩ = y := by
      -- There are at least k - i ≥ 1 elements of t not in t_before_i
      have : (t \ t_before_i).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h_empty
        have : (t \ t_before_i).card = 0 := by simp [h_empty]
        omega
      obtain ⟨y, hy⟩ := this
      use y
      constructor
      · exact Finset.mem_of_mem_sdiff hy
      · -- y ∈ t and y ∉ t_before_i, so y is not in first i positions
        have hy_in_sorted : y ∈ sorted := by
          exact (List.Perm.mem_iff h_perm).2 (by
            simpa [Finset.mem_toList] using ht_sub (Finset.mem_of_mem_sdiff hy))
        obtain ⟨j, hj, hyj⟩ := List.mem_iff_getElem.mp hy_in_sorted
        use j
        constructor
        · -- Show j ≥ i
          by_contra hj_lt_i
          push_neg at hj_lt_i
          -- If j < i, then y ∈ sorted.take i
          have : y ∈ sorted.take i := by
            refine (List.mem_iff_getElem).2 ?_
            refine ⟨j, ?_, ?_⟩
            ·
              have : j < min i sorted.length := lt_min_iff.mpr ⟨hj_lt_i, hj⟩
              simpa [List.length_take] using this
            · simpa [List.getElem_take] using hyj
          -- So y ∈ t_before_i
          have : y ∈ t_before_i := by
            simp [t_before_i, Finset.mem_inter, List.mem_toFinset, this]
            exact Finset.mem_of_mem_sdiff hy
          -- But y ∈ t \ t_before_i, contradiction
          exact Finset.not_mem_sdiff_of_mem this hy
        · exact ⟨hj, hyj⟩

    obtain ⟨y, hy_in_t, j, hj_ge_i, hj_lt, hyj⟩ := h_exists_t_after_i

    -- Now we have:
    -- - x at position i, x ∈ s\t
    -- - y at position j ≥ i, y ∈ t
    -- By h_scores: score y > score x
    have h_score_y_gt_x : score y > score x := h_scores y hy_in_t x hx_in_sdiff

    -- But if j > i, by sorted property: score(sorted[i]) > score(sorted[j])
    -- i.e., score x > score y
    by_cases h_j_eq_i : j = i
    · -- If j = i, then sorted[i] = x and sorted[i] = y, so x = y
      subst h_j_eq_i
      have hxi' : sorted.get ⟨j, hj_lt⟩ = x := by
        simpa using hxi
      have : x = y := by
        rw [← hxi', ← hyj]
      -- But x ∈ s\t and y ∈ t, contradiction
      rw [this] at hx_in_sdiff
      exact Finset.not_mem_sdiff_of_mem hy_in_t hx_in_sdiff
    · -- If j > i, use sorted property
      have hj_gt_i : i < j := lt_of_le_of_ne hj_ge_i (Ne.symm h_j_eq_i)
      have h_sorted_order : score (sorted.get ⟨i, hi_lt⟩) ≥ score (sorted.get ⟨j, hj_lt⟩) := by
        have hj_fin : (⟨i, hi_lt⟩ : Fin sorted.length) < ⟨j, hj_lt⟩ := by
          simpa using hj_gt_i
        exact List.Pairwise.rel_get_of_lt h_sorted hj_fin
      rw [hxi, hyj] at h_sorted_order
      -- So score x > score y, contradicting score y > score x
      omega

  · -- If x ∈ t, then x ∈ (sorted.take k).toFinset
    intro hx_in_t
    rw [List.mem_toFinset, List.mem_take]

    -- x is in s, so x is in sorted
    have hx_in_sorted : x ∈ sorted := by
      exact (List.Perm.mem_iff h_perm).2 (by
        simpa [Finset.mem_toList] using ht_sub hx_in_t)

    -- Find position of x in sorted
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx_in_sorted
    use i
    constructor
    · -- Show i < k
      by_contra hi_ge_k
      push_neg at hi_ge_k

      -- Key insight: exactly k elements of sorted are in t (by counting lemma)
      have h_count_t : (sorted.filter (fun y => y ∈ t)).length = k :=
        count_subset_in_perm s t sorted k ht_sub ht_card h_perm

      -- Elements of t in first k positions
      let t_in_first_k := (sorted.take k).filter (fun y => decide (y ∈ t))

      -- Elements of t after first k positions
      let t_after_k := (sorted.drop k).filter (fun y => decide (y ∈ t))

      -- Total elements of t = elements in first k + elements after k
      have h_partition : t_in_first_k.length + t_after_k.length = k := by
        have h_split : sorted.filter (fun y => y ∈ t) = t_in_first_k ++ t_after_k := by
          rw [← List.filter_append]
          congr 1
          exact (List.take_append_drop k sorted).symm
        calc
          t_in_first_k.length + t_after_k.length
              = (t_in_first_k ++ t_after_k).length := by simp [List.length_append]
          _ = (sorted.filter (fun y => y ∈ t)).length := by simpa [h_split]
          _ = k := h_count_t

      -- x is in t and at position i ≥ k, so x ∈ t_after_k
      have hx_in_after : x ∈ t_after_k := by
        simp [t_after_k, List.mem_filter]
        constructor
        · -- show x ∈ sorted.drop k
          refine (List.mem_iff_getElem).2 ?_
          refine ⟨i - k, ?_, ?_⟩
          · -- i - k < (sorted.drop k).length
            have hi_lt_len : i < sorted.length := hi
            have hk_le_i : k ≤ i := hi_ge_k
            have : i - k < sorted.length - k := by
              omega
            have hi_drop : i - k < (sorted.drop k).length := by
              simpa [List.length_drop] using this
            exact hi_drop
          · -- (sorted.drop k)[i - k] = x
            have hi_drop : i - k < (sorted.drop k).length := by
              have : i - k < sorted.length - k := by omega
              simpa [List.length_drop] using this
            have hdrop : (sorted.drop k)[i - k] = sorted[k + (i - k)] := by
              simpa using (List.getElem_drop (xs := sorted) (i := k) (j := i - k) (h := hi_drop))
            have hx' : sorted[(i - k) + k] = x := by
              simpa [Nat.sub_add_cancel hi_ge_k] using hxi
            have hx'' : sorted[k + (i - k)] = x := by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx'
            exact hdrop.trans hx''
        · exact hx_in_t

      -- So t_after_k is nonempty, meaning t_after_k.length ≥ 1
      have h_after_pos : t_after_k.length ≥ 1 := by
        have h_ne : t_after_k ≠ [] := List.ne_nil_of_mem hx_in_after
        have hpos : 0 < t_after_k.length := List.length_pos_of_ne_nil h_ne
        exact Nat.succ_le_iff.mpr hpos

      -- From partition: t_in_first_k.length = k - t_after_k.length ≤ k - 1
      have h_first_k_count : t_in_first_k.length ≤ k - 1 := by
        have h_le : t_in_first_k.length + 1 ≤ k := by
          have := Nat.add_le_add_left h_after_pos t_in_first_k.length
          -- t_in_first_k.length + 1 ≤ t_in_first_k.length + t_after_k.length
          simpa [h_partition] using this
        exact Nat.le_sub_of_add_le h_le

      -- Now the key: all elements of s\t have lower scores than all elements of t
      -- In a descending sorted list, higher scores come first
      -- So all k elements of t should appear before all elements of s\t
      -- This means all k elements of t should be in the first k positions
      -- But we just showed at most k-1 elements of t are in the first k positions
      -- Contradiction!

      -- Since t_in_first_k.length ≤ k-1 and (sorted.take k).length = min k sorted.length,
      -- there must be at least one element of s\t in the first k positions
      have h_sdiff_in_first_k : ∃ y, y ∈ (sorted.take k) ∧ y ∈ s \ t := by
        -- Count elements in first k positions
        have h_take_length : (sorted.take k).length = k := by
          rw [List.length_take, h_length]
          simp [hs_card]
        -- Elements in first k are either in t or in s\t
        -- We have at most k-1 in t, so at least 1 in s\t
        by_contra h_none
        push_neg at h_none
        -- All elements in first k are in t
        have : ∀ y ∈ sorted.take k, y ∈ t := by
          intro y hy
          have hy_in_s : y ∈ s := by
            have : y ∈ sorted := List.mem_of_mem_take hy
            have : y ∈ s.toList := (List.Perm.mem_iff h_perm).1 this
            exact Finset.mem_toList.mp this
          by_contra hy_not_t
          have : y ∈ s \ t := Finset.mem_sdiff.mpr ⟨hy_in_s, hy_not_t⟩
          exact h_none y hy this
        -- So all k elements in first k positions are in t
        have : t_in_first_k.length = k := by
          have h_all_in_t : ∀ y ∈ sorted.take k, y ∈ t := this
          -- t_in_first_k is (sorted.take k).filter (fun y => y ∈ t)
          -- Since all elements of sorted.take k are in t, filter doesn't remove anything
          unfold t_in_first_k
          have : (sorted.take k).filter (fun y => decide (y ∈ t)) = sorted.take k := by
            apply List.filter_eq_self.2
            intro y hy
            have hy_t : y ∈ t := h_all_in_t y hy
            simpa using hy_t
          rw [this, h_take_length]
        omega

      obtain ⟨y, hy_in_take, hy_in_sdiff⟩ := h_sdiff_in_first_k

      -- y is in s\t and in first k positions, x is in t and after position k
      -- Find their positions
      obtain ⟨j, hj_lt_k, hj_lt_len, hyj⟩ := (List.mem_take).1 hy_in_take
      have hyj' : sorted.get ⟨j, hj_lt_len⟩ = y := by
        simpa using hyj

      -- We have j < k ≤ i
      -- By h_scores: score x > score y
      have h_score_x_gt_y : score x > score y := h_scores x hx_in_t y hy_in_sdiff

      -- But sorted is pairwise descending, so score(sorted[j]) ≥ score(sorted[i])
      have h_sorted_order : score (sorted.get ⟨j, hj_lt_len⟩) ≥ score (sorted.get ⟨i, hi⟩) := by
        have h_rel := List.pairwise_iff_get.mp h_sorted
        have hj_lt_i : j < i := Nat.lt_of_lt_of_le hj_lt_k hi_ge_k
        exact h_rel ⟨j, hj_lt_len⟩ ⟨i, hi⟩ hj_lt_i

      -- sorted[j] = y and sorted[i] = x
      have : sorted.get ⟨j, hj_lt_len⟩ = y := hyj'
      have : sorted.get ⟨i, hi⟩ = x := hxi

      -- So score y ≥ score x, contradicting score x > score y
      have h_y_ge_x : score y ≥ score x := by
        have hxi' : sorted.get ⟨i, hi⟩ = x := by
          simpa using hxi
        have hyj'' : score y = score (sorted.get ⟨j, hj_lt_len⟩) := by
          rw [hyj']
        have hxi'' : score (sorted.get ⟨i, hi⟩) = score x := by
          rw [hxi']
        calc
          score y = score (sorted.get ⟨j, hj_lt_len⟩) := hyj''
          _ ≥ score (sorted.get ⟨i, hi⟩) := h_sorted_order
          _ = score x := hxi''
      exact (not_lt_of_ge h_y_ge_x) h_score_x_gt_y
    · exact ⟨hi, hxi⟩

/-- 如果子集t至少有k个元素，且t的所有元素分数都高于s\t的所有元素，
    则从s中选出的前k个元素都在t中 -/
lemma top_k_subset_of_high_scores {α : Type*} [DecidableEq α] [Fintype α]
    (s : Finset α) (t : Finset α) (score : α → ℕ) (k : ℕ)
    (ht_sub : t ⊆ s)
    (ht_card : k ≤ t.card)
    (h_scores : ∀ x ∈ t, ∀ y ∈ s \ t, score x > score y) :
    let sorted := s.toList.mergeSort (fun a b => decide (score a ≥ score b))
    (sorted.take k).toFinset ⊆ t := by
  intro sorted
  intro x hx
  by_contra hx_not_t
  -- x is in top k but not in t, so x ∈ s \ t
  have hx_in_s : x ∈ s := by
    have : x ∈ sorted := by
      rw [List.mem_toFinset] at hx
      exact List.mem_of_mem_take hx
    have h_perm := List.mergeSort_perm s.toList (fun a b => decide (score a ≥ score b))
    have : x ∈ s.toList := (List.Perm.mem_iff h_perm).1 this
    exact Finset.mem_toList.mp this
  have hx_in_sdiff : x ∈ s \ t := Finset.mem_sdiff.mpr ⟨hx_in_s, hx_not_t⟩

  -- Find position of x in sorted
  rw [List.mem_toFinset] at hx
  have hx_take : x ∈ sorted.take k := hx
  obtain ⟨i, hi_lt_len, hxi⟩ := List.mem_iff_getElem.mp hx_take
  have hi_lt_k : i < k := by
    have h_len : (sorted.take k).length = min k sorted.length := by
      simpa using (List.length_take k sorted)
    have hi_lt_min : i < min k sorted.length := by
      simpa [h_len] using hi_lt_len
    exact lt_of_lt_of_le hi_lt_min (Nat.min_le_left _ _)

  have hi_sorted : i < sorted.length := by
    have h_take_len : (sorted.take k).length ≤ sorted.length := by
      simpa [List.length_take] using (Nat.min_le_right k sorted.length)
    exact lt_of_lt_of_le hi_lt_len h_take_len

  have hxi_sorted : sorted[i] = x := by
    have h_take : (sorted.take k)[i]? = sorted[i]? := by
      simpa using (getElem?_take_of_lt' sorted (n := k) (i := i) hi_lt_k)
    have hxi_opt : (sorted.take k)[i]? = some x := by
      rw [List.getElem?_eq_getElem hi_lt_len]
      simpa [hxi]
    have : sorted[i]? = some x := by
      simpa [h_take] using hxi_opt
    simpa [List.getElem?_eq_getElem hi_sorted] using this

  have h_perm : sorted.Perm s.toList :=
    List.mergeSort_perm s.toList (fun a b => decide (score a ≥ score b))
  haveI : Std.Total (fun a b : α => score a ≥ score b) :=
    ⟨by intro a b; exact le_total _ _⟩
  haveI : IsTrans α (fun a b : α => score a ≥ score b) :=
    ⟨by intro a b c hab hbc; exact le_trans hbc hab⟩
  have h_sorted : sorted.Pairwise (fun a b => score a ≥ score b) := by
    simpa [sorted] using
      (List.pairwise_mergeSort' (r := fun a b => score a ≥ score b) s.toList)

  -- There are at least k elements of t in sorted
  have h_t_count : k ≤ (sorted.filter (fun y => y ∈ t)).length := by
    have : (sorted.filter (fun y => y ∈ t)).length = t.card := by
      have h_count := count_subset_in_perm s t sorted t.card ht_sub rfl h_perm
      exact h_count
    simpa [this] using ht_card

  -- At least one element of t must be at position ≥ i
  have h_exists_t_after_i :
      ∃ y ∈ t, ∃ j, j ≥ i ∧ j < sorted.length ∧ sorted[j]? = some y := by
    -- Count elements of t in first i positions
    let t_before_i := (sorted.take i).filter (fun y => y ∈ t)
    have h_before_count : t_before_i.length ≤ i := by
      unfold t_before_i
      have h_le_take : t_before_i.length ≤ (sorted.take i).length := List.length_filter_le _ _
      have h_take_le : (sorted.take i).length ≤ i := by
        simpa [List.length_take] using (Nat.min_le_left i sorted.length)
      exact le_trans h_le_take h_take_le

    -- Elements of t in sorted list
    let t_in_sorted := sorted.filter (fun y => y ∈ t)
    have h_t_count_internal : t_in_sorted.length = t.card := by
      unfold t_in_sorted
      exact count_subset_in_perm s t sorted t.card ht_sub rfl h_perm

    -- Partition: t_in_sorted = t_before_i ++ t_after_i
    let t_after_i := (sorted.drop i).filter (fun y => y ∈ t)
    have h_partition : t_in_sorted = t_before_i ++ t_after_i := by
      unfold t_in_sorted t_before_i t_after_i
      rw [← List.filter_append, List.take_append_drop]

    have h_before_lt : t_before_i.length < t.card := by
      have hi_lt_t : i < t.card := lt_of_lt_of_le hi_lt_k ht_card
      exact lt_of_le_of_lt h_before_count hi_lt_t

    have h_after_nonempty : t_after_i ≠ [] := by
      intro h_nil
      have h_len_eq : t_before_i.length = t.card := by
        have : t_in_sorted.length = t_before_i.length := by
          simpa [h_partition, h_nil] using rfl
        simpa [h_t_count_internal] using this.symm
      have h_contra : t_before_i.length < t_before_i.length := by
        simpa [h_len_eq] using h_before_lt
      exact (lt_irrefl _ h_contra)

    -- Get an element from t_after_i
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ h_after_nonempty

    use y
    constructor
    · -- y ∈ t
      have : y ∈ t_after_i := hy
      unfold t_after_i at this
      have h_mem : y ∈ sorted.drop i ∧ y ∈ t := by
        simpa [List.mem_filter] using this
      exact h_mem.2
    · -- Find position j of y in sorted
      have hy_in_sorted : y ∈ sorted := by
        have : y ∈ t_after_i := hy
        unfold t_after_i at this
        have h_mem : y ∈ sorted.drop i ∧ y ∈ t := by
          simpa [List.mem_filter] using this
        have : y ∈ sorted.drop i := h_mem.1
        exact mem_of_mem_drop this
      obtain ⟨j, hj, hyj⟩ := List.mem_iff_getElem.mp hy_in_sorted
      use j
      constructor
      · -- j ≥ i
        by_contra hj_not_le
        have hj_lt_i : j < i := Nat.lt_of_not_ge hj_not_le
        have hy_in_take : y ∈ sorted.take i := by
          have hj_lt_len : j < (sorted.take i).length := by
            have hj_lt_min : j < min i sorted.length := by
              exact (lt_min_iff.mpr ⟨hj_lt_i, hj⟩)
            simpa [List.length_take] using hj_lt_min
          have : (sorted.take i)[j]? = some y := by
            have : sorted[j]? = some y := by
              rw [List.getElem?_eq_getElem hj]
              simpa [hyj]
            have h_take : (sorted.take i)[j]? = sorted[j]? := by
              simpa using (getElem?_take_of_lt' sorted (n := i) (i := j) hj_lt_i)
            simpa [h_take] using this
          have hget : (sorted.take i)[j] = y := by
            have : some (sorted.take i)[j] = some y := by
              simpa [List.getElem?_eq_getElem hj_lt_len] using this
            exact Option.some.inj this
          exact (List.mem_iff_getElem).2 ⟨j, hj_lt_len, hget⟩
        have h_sorted_nodup : sorted.Nodup :=
          (List.Perm.nodup_iff h_perm).2 (Finset.nodup_toList s)
        have h_disjoint : List.Disjoint (sorted.take i) (sorted.drop i) := by
          have := List.disjoint_of_nodup_append (l₁ := sorted.take i) (l₂ := sorted.drop i)
          apply this
          simpa [List.take_append_drop] using h_sorted_nodup
        have hy_in_drop : y ∈ sorted.drop i := by
          have : y ∈ t_after_i := hy
          unfold t_after_i at this
          have h_mem : y ∈ sorted.drop i ∧ y ∈ t := by
            simpa [List.mem_filter] using this
          exact h_mem.1
        exact (h_disjoint hy_in_take hy_in_drop).elim
      · exact ⟨hj, by simpa [List.getElem?_eq_getElem hj, hyj]⟩

  obtain ⟨y, hy_in_t, j, hj_ge_i, hj_lt, hyj⟩ := h_exists_t_after_i


  -- y ∈ t and x ∈ s \ t, so score y > score x
  have h_score_y_gt_x : score y > score x := h_scores y hy_in_t x hx_in_sdiff

  -- But if j > i, by sorted property: score(sorted[i]) ≥ score(sorted[j])
  by_cases h_j_eq_i : j = i
  · -- If j = i, then x = y, contradiction
    have hj_lt' : i < sorted.length := by simpa [h_j_eq_i] using hj_lt
    have hyj' : sorted[i] = y := by
      simpa [h_j_eq_i, List.getElem?_eq_getElem hj_lt'] using hyj
    have : x = y := by
      calc
        x = sorted[i] := hxi_sorted.symm
        _ = y := hyj'
    rw [this] at hx_not_t
    exact hx_not_t hy_in_t
  · -- If j > i, use sorted property
    have hj_gt_i : i < j := lt_of_le_of_ne hj_ge_i (Ne.symm h_j_eq_i)
    have h_sorted_order :
        score (sorted.get ⟨i, hi_sorted⟩) ≥ score (sorted.get ⟨j, hj_lt⟩) := by
      have h_rel := List.pairwise_iff_get.mp h_sorted
      exact h_rel ⟨i, hi_sorted⟩ ⟨j, hj_lt⟩ hj_gt_i
    have hyj' : sorted.get ⟨j, hj_lt⟩ = y := by
      simpa [List.getElem?_eq_getElem hj_lt] using hyj
    have hyj'' : sorted[j] = y := by
      simpa [List.getElem?_eq_getElem hj_lt] using hyj
    have hxy : score x ≥ score y := by
      simpa [hxi_sorted, hyj''] using h_sorted_order
    exact (not_lt_of_ge hxy) h_score_y_gt_x

/-- 如果x在有限集合S中具有最大分数，且k ≥ 1，则x在computeTopHalf的结果中 -/
lemma max_score_in_computeTopHalf
    (setup : CompetitionSetup Student Subject) (sub : Subject) (S : Finset Student) (x : Student) (k : ℕ)
    (hx_in_S : x ∈ S)
    (hx_max : ∀ y ∈ S, setup.score sub y ≤ setup.score sub x)
    (hk_pos : k ≥ 1)
    (hk_le_card : k ≤ S.card)
    (hk_eq : k = S.card / 2) :
    x ∈ computeTopHalf setup sub S := by
  classical
  unfold computeTopHalf
  set sorted := S.toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))
  -- We'll prove membership in `sorted.take k`, then rewrite.

  have hx_in_sorted : x ∈ sorted := by
    have h_perm := List.mergeSort_perm S.toList (fun a b => decide (setup.score sub a ≥ setup.score sub b))
    have : x ∈ S.toList := Finset.mem_toList.mpr hx_in_S
    exact (List.Perm.mem_iff h_perm.symm).1 this

  obtain ⟨i, hi_lt, hxi⟩ := List.mem_iff_getElem.mp hx_in_sorted

  have h_sorted : sorted.Pairwise (fun a b => setup.score sub a ≥ setup.score sub b) := by
    haveI : Std.Total (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
      ⟨by intro a b; exact le_total _ _⟩
    haveI : IsTrans Student (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
      ⟨by intro a b c hab hbc; exact le_trans hbc hab⟩
    simpa [sorted] using
      (List.pairwise_mergeSort' (r := fun a b => setup.score sub a ≥ setup.score sub b) S.toList)
  have h_nodup : sorted.Nodup := by
    simpa [sorted] using
      (List.nodup_mergeSort (l := S.toList)
        (le := fun a b => decide (setup.score sub a ≥ setup.score sub b))).2
      (Finset.nodup_toList S)

  have hi_eq_0 : i = 0 := by
    by_contra h_ne
    have hi_pos : 0 < i := Nat.pos_of_ne_zero h_ne
    have hlen_pos : 0 < sorted.length := List.length_pos_of_mem hx_in_sorted
    let y : Student := sorted.get ⟨0, by simpa using hlen_pos⟩
    have hy_in_S : y ∈ S := by
      have : y ∈ sorted := by
        have : y ∈ sorted.take 1 := by
          refine (List.mem_take).2 ?_
          refine ⟨0, Nat.succ_pos _, ?_⟩
          refine ⟨hlen_pos, ?_⟩
          rfl
        exact List.mem_of_mem_take this
      have h_perm := List.mergeSort_perm S.toList (fun a b => decide (setup.score sub a ≥ setup.score sub b))
      have : y ∈ S.toList := (List.Perm.mem_iff h_perm).1 this
      exact Finset.mem_toList.mp this
    have h_sorted_order : setup.score sub x ≤ setup.score sub y := by
      have hfin : (⟨0, hlen_pos⟩ : Fin sorted.length) < ⟨i, hi_lt⟩ := by
        simpa using hi_pos
      have h_sorted_order' :
          setup.score sub (sorted.get ⟨0, hlen_pos⟩) ≥ setup.score sub (sorted.get ⟨i, hi_lt⟩) :=
        List.Pairwise.rel_get_of_lt h_sorted hfin
      have hxi' : sorted.get ⟨i, hi_lt⟩ = x := by
        simpa using hxi
      calc
        setup.score sub x = setup.score sub (sorted.get ⟨i, hi_lt⟩) := by
          rw [hxi']
        _ ≤ setup.score sub (sorted.get ⟨0, hlen_pos⟩) := by
          simpa using h_sorted_order'
        _ = setup.score sub y := by
          rfl
    have h_score_y_le_x : setup.score sub y ≤ setup.score sub x := hx_max y hy_in_S
    have h_score_eq : setup.score sub y = setup.score sub x :=
      le_antisymm h_score_y_le_x h_sorted_order
    have h_y_eq_x : y = x := (setup.score_injective sub) h_score_eq
    have hxi' : sorted.get ⟨i, hi_lt⟩ = x := by
      simpa using hxi
    have h_inj : Function.Injective sorted.get := (List.nodup_iff_injective_get.mp h_nodup)
    have h_idx_eq : (⟨0, hlen_pos⟩ : Fin sorted.length) = ⟨i, hi_lt⟩ := by
      apply h_inj
      calc
        sorted.get ⟨0, hlen_pos⟩ = y := rfl
        _ = x := h_y_eq_x
        _ = sorted.get ⟨i, hi_lt⟩ := by symm; exact hxi'
    have : (0 : Nat) = i := by
      simpa using congrArg Fin.val h_idx_eq
    exact (ne_of_lt hi_pos) this

  have hi_lt_k : i < k := by
    rw [hi_eq_0]
    exact lt_of_lt_of_le (Nat.succ_pos _) hk_pos

  have hx_in_take : x ∈ (sorted.take k).toFinset := by
    rw [List.mem_toFinset, List.mem_take]
    refine ⟨i, hi_lt_k, ?_⟩
    refine ⟨hi_lt, ?_⟩
    simpa using hxi
  simpa [sorted, hk_eq] using hx_in_take

/-- 辅助引理：如果两个幸存者集合的交集大小为2，
    则某些排列可能产生相同的冠军 -/
lemma size_two_intersection_property
    (setup : CompetitionSetup Student Subject)
    (s1 s2 s3 : Subject) (hs12 : s1 ≠ s2) (hs23 : s2 ≠ s3) (hs13 : s1 ≠ s3) :
  let S1 := survivalSet setup s1
  let S2 := survivalSet setup s2
  (S1 ∩ S2).card = 2 →
  ∃ (winner : Student),
    Survives setup [s1, s2, s3] winner ∧ Survives setup [s2, s1, s3] winner := by
  intro S1 S2 h_inter_2

  -- 设I = S1 ∩ S2，|I| = 2
  let I := S1 ∩ S2

  -- 关键观察：I中的学生在两个科目上的排名都≤4
  -- S1\I中的学生在s2上的排名>4
  -- S2\I中的学生在s1上的排名>4

  -- 对于排列[s1, s2, s3]：
  -- 第一轮后幸存S1
  -- 第二轮：从S1中选s2分数最高的2个
  -- 由于I⊆S2且S1\I∩S2=∅，I中的学生s2排名≤4，S1\I中的学生s2排名>4
  -- 因此I中的学生s2分数都比S1\I中的高
  -- 所以第二轮后幸存的恰好是I

  unfold Survives
  simp only []

  -- 计算第一个排列的结果
  let S0 := (univ : Finset Student)
  let S1_round1 := computeTopHalf setup s1 S0
  let S1_round2 := computeTopHalf setup s2 S1_round1
  let S1_round3 := computeTopHalf setup s3 S1_round2

  -- 计算第二个排列的结果
  let S2_round1 := computeTopHalf setup s2 S0
  let S2_round2 := computeTopHalf setup s1 S2_round1
  let S2_round3 := computeTopHalf setup s3 S2_round2

  -- 关键：证明S1_round2 = I 且 S2_round2 = I
  -- 然后S1_round3和S2_round3都是从I中选s3分数最高的1个

  -- 由于完整证明需要大量关于computeTopHalf的技术性引理，
  -- 而这些引理涉及mergeSort、take、toFinset的复杂交互，
  -- 我们使用以下策略：

  -- 核心数学事实：
  -- 1. S1_round1 = S1（由survivalSet的定义）
  -- 2. 从S1中选s2分数最高的2个，由于|I|=2且I中的学生s2分数都比S1\I中的高，
  --    结果是I
  -- 3. 类似地，S2_round2 = I
  -- 4. 从I中选s3分数最高的1个，两个排列得到相同的结果

  -- 为了形式化这一点，我们需要证明computeTopHalf在特定条件下的行为
  -- 这需要以下引理（省略详细证明）：

  have h_S1_round1 : S1_round1 = S1 := by
    unfold S1_round1 S1 survivalSet
    rfl

  -- 证明S1_round2 = I需要详细分析computeTopHalf
  -- 关键是：I中的学生在s2上的排名都≤4（因为I⊆S2）
  -- S1\I中的学生在s2上的排名都>4（因为它们不在S2中）
  -- 因此按s2分数排序时，I中的学生都排在S1\I中的学生前面
  -- 取前2个（因为S1.card/2 = 4/2 = 2）得到I

  have h_I_in_S2 : I ⊆ S2 := Finset.inter_subset_right
  have h_I_in_S1 : I ⊆ S1 := Finset.inter_subset_left

  have h_S1_diff_not_in_S2 : ∀ x ∈ S1 \ I, x ∉ S2 := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    intro hx_in_S2
    have : x ∈ I := Finset.mem_inter.mpr ⟨hx.1, hx_in_S2⟩
    exact hx.2 this

  -- 由于I中的学生在S2中（s2排名≤4），S1\I中的学生不在S2中（s2排名>4）
  -- 根据rank的定义，I中的学生s2分数更高

  have h_I_better_s2 : ∀ u ∈ I, ∀ v ∈ S1 \ I, setup.score s2 u > setup.score s2 v := by
    intro u hu v hv
    have hu_in_S2 : u ∈ S2 := h_I_in_S2 hu
    have hv_not_S2 : v ∉ S2 := h_S1_diff_not_in_S2 v hv
    -- u在S2中意味着u的s2排名≤4
    have hu_rank : rank setup s2 u ≤ 4 :=
      (rank_le_four_iff_in_survival setup s2 u).2 hu_in_S2
    -- v不在S2中意味着v的s2排名>4
    have hv_rank : rank setup s2 v > 4 := by
      exact not_in_survival_implies_rank_gt_four setup s2 v hv_not_S2
    -- 排名更小意味着分数更高
    unfold rank at hu_rank hv_rank
    -- rank u = |{t : u的分数 < t的分数}| + 1 ≤ 4
    -- rank v = |{t : v的分数 < t的分数}| + 1 > 4
    -- 需要证明：u的分数 > v的分数
    -- 如果u的分数 ≤ v的分数，则v会在"分数>u的分数"的集合中
    -- 这会使得rank u增加
    by_contra h_not_greater
    push_neg at h_not_greater
    -- u的分数 ≤ v的分数
    have h_subset :
        (univ.filter (fun t => setup.score s2 t > setup.score s2 v)) ⊆
        (univ.filter (fun t => setup.score s2 t > setup.score s2 u)) := by
      intro t ht
      have ht' : setup.score s2 t > setup.score s2 v := by
        simpa [Finset.mem_filter] using ht
      have : setup.score s2 t > setup.score s2 u := lt_of_le_of_lt h_not_greater ht'
      simp [Finset.mem_filter, this, Finset.mem_univ]
    have h_card_le :
        (univ.filter (fun t => setup.score s2 t > setup.score s2 v)).card ≤
        (univ.filter (fun t => setup.score s2 t > setup.score s2 u)).card :=
      Finset.card_le_card h_subset
    have h_rank_le : rank setup s2 v ≤ rank setup s2 u := by
      unfold rank
      exact Nat.add_le_add_right h_card_le 1
    have : rank setup s2 v ≤ 4 := le_trans h_rank_le hu_rank
    exact (not_lt_of_ge this) hv_rank

  -- 现在我们知道I中的学生s2分数都比S1\I中的高
  -- 且|I|=2，S1.card=4
  -- 从S1中选s2分数最高的2个应该得到I

  -- 关键：使用helper lemma证明computeTopHalf setup s2 S1 = I
  have h_S1_card : S1.card = 4 := by
    simpa [S1] using (survivalSet_card setup s1)

  have h_I_card : I.card = 2 := h_inter_2

  -- 应用top_k_equals_high_score_subset
  have h_S1_round2_eq_I : S1_round2 = I := by
    unfold S1_round2
    rw [h_S1_round1]
    -- 使用helper lemma
    have h_apply := top_k_equals_high_score_subset S1 I (setup.score s2) 2
      (Finset.inter_subset_left) h_I_card (by omega : 2 ≤ S1.card) h_I_better_s2
    simpa [computeTopHalf, h_S1_card] using h_apply

  -- 类似地证明S2_round2 = I (需要先证明I中元素s1分数比S2\I高)
  have h_I_better_s1 : ∀ u ∈ I, ∀ v ∈ S2 \ I, setup.score s1 u > setup.score s1 v := by
    intro u hu v hv
    have hu_in_S1 : u ∈ S1 := h_I_in_S1 hu
    have hv_not_S1 : v ∉ S1 := by
      intro hv_in_S1
      have : v ∈ I := Finset.mem_inter.mpr ⟨hv_in_S1, Finset.mem_of_mem_sdiff hv⟩
      exact Finset.not_mem_sdiff_of_mem this hv
    have hu_rank : rank setup s1 u ≤ 4 :=
      (rank_le_four_iff_in_survival setup s1 u).2 hu_in_S1
    have hv_rank : rank setup s1 v > 4 := by
      exact not_in_survival_implies_rank_gt_four setup s1 v hv_not_S1
    unfold rank at hu_rank hv_rank
    by_contra h_not_greater
    push_neg at h_not_greater
    have h_subset :
        (univ.filter (fun t => setup.score s1 t > setup.score s1 v)) ⊆
        (univ.filter (fun t => setup.score s1 t > setup.score s1 u)) := by
      intro t ht
      have ht' : setup.score s1 t > setup.score s1 v := by
        simpa [Finset.mem_filter] using ht
      have : setup.score s1 t > setup.score s1 u := lt_of_le_of_lt h_not_greater ht'
      simp [Finset.mem_filter, this, Finset.mem_univ]
    have h_card_le :
        (univ.filter (fun t => setup.score s1 t > setup.score s1 v)).card ≤
        (univ.filter (fun t => setup.score s1 t > setup.score s1 u)).card :=
      Finset.card_le_card h_subset
    have h_rank_le : rank setup s1 v ≤ rank setup s1 u := by
      unfold rank
      exact Nat.add_le_add_right h_card_le 1
    have : rank setup s1 v ≤ 4 := le_trans h_rank_le hu_rank
    exact (not_lt_of_ge this) hv_rank

  have h_S2_card : S2.card = 4 := by
    simpa [S2] using (survivalSet_card setup s2)

  have h_S2_round2_eq_I : S2_round2 = I := by
    unfold S2_round2
    have h_S2_round1 : S2_round1 = S2 := by unfold S2_round1 S2 survivalSet; rfl
    rw [h_S2_round1]
    -- 使用helper lemma
    have h_apply := top_k_equals_high_score_subset S2 I (setup.score s1) 2
      (Finset.inter_subset_right) h_I_card (by omega : 2 ≤ S2.card) h_I_better_s1
    have h_S2_card : S2.card = 4 := by
      simpa [S2] using (survivalSet_card setup s2)
    simpa [computeTopHalf, h_S2_card] using h_apply

  -- 现在两个排列都从I中选s3分数最高的1个
  have h_final_eq : S1_round3 = S2_round3 := by
    unfold S1_round3 S2_round3
    rw [h_S1_round2_eq_I, h_S2_round2_eq_I]

  -- I中必有元素（因为|I|=2）
  have h_I_nonempty : I.Nonempty := by
    have : 0 < I.card := by
      simpa [h_I_card] using (Nat.succ_pos 1)
    exact Finset.card_pos.mp this

  -- 从I中选s3分数最高的1个，两个排列得到相同的学生
  -- 选出的学生就是winner
  have h_S1_round3_card : S1_round3.card = 1 := by
    unfold S1_round3
    rw [h_S1_round2_eq_I]
    simpa [h_I_card] using (computeTopHalf_card setup s3 I)

  have h_S1_round3_nonempty : S1_round3.Nonempty := by
    have : 0 < S1_round3.card := by
      simpa [h_S1_round3_card] using (Nat.succ_pos 0)
    exact Finset.card_pos.mp this

  -- 由于S1_round3.card = 1，它恰好包含一个元素
  have h_exists_unique : ∃! winner, winner ∈ S1_round3 := by
    classical
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h_S1_round3_card
    refine ⟨w, ?_, ?_⟩
    · simpa [hw]
    · intro w' hw'
      have : w' ∈ ({w} : Finset Student) := by
        simpa [hw] using hw'
      simpa using this

  obtain ⟨winner, h_winner, h_unique⟩ := h_exists_unique
  use winner
  constructor
  · exact h_winner
  ·
    have h_in_S2 : winner ∈ S2_round3 := by
      simpa [h_final_eq] using h_winner
    have h_in_S2' : winner ∈ computeTopHalf setup s3 S2_round2 := by
      simpa [S2_round3] using h_in_S2
    have h_in_S2'' : winner ∈ computeTopHalf setup s3 I := by
      simpa [h_S2_round2_eq_I] using h_in_S2'
    have h_in_S2''' :
        winner ∈ computeTopHalf setup s3 (computeTopHalf setup s1 (computeTopHalf setup s2 univ)) := by
      have h_in_S2'''' : winner ∈ computeTopHalf setup s3 S2_round2 := by
        simpa [h_S2_round2_eq_I] using h_in_S2''
      simpa [S2_round2, S2_round1, S0] using h_in_S2''''
    -- Now show Survives for [s2, s1, s3]
    simpa [Survives, S0] using h_in_S2'''

/-- 辅助函数：计算元素属于多少个集合 -/
def membershipCount {U : Type*} [DecidableEq U] (x : U) (S1 S2 S3 : Finset U) : ℕ :=
  (if x ∈ S1 then 1 else 0) + (if x ∈ S2 then 1 else 0) + (if x ∈ S3 then 1 else 0)

/-- 辅助函数：恰好属于k个集合的元素集合 -/
def exactlyInKSets {U : Type*} [Fintype U] [DecidableEq U]
    (k : ℕ) (S1 S2 S3 : Finset U) : Finset U :=
  univ.filter (fun x => membershipCount x S1 S2 S3 = k)

/-- 引理：交集下界 - 包含排斥原理的应用
    对于8个元素的全集中的三个大小为4的子集，
    它们的两两交集大小之和至少为4 -/
lemma intersection_lower_bound :
  ∀ (U : Type*) [Fintype U] [DecidableEq U] (hU : Fintype.card U = 8)
    (S1 S2 S3 : Finset U)
    (h1 : S1.card = 4) (h2 : S2.card = 4) (h3 : S3.card = 4),
  (S1 ∩ S2).card + (S2 ∩ S3).card + (S3 ∩ S1).card ≥ 4 := by
  intro U _ _ hU S1 S2 S3 h1 h2 h3

  -- 关键：使用包含排斥原理
  -- |S1 ∪ S2 ∪ S3| ≤ 8 (因为是8元素全集的子集)
  have union_bound : (S1 ∪ S2 ∪ S3).card ≤ 8 := by
    have : S1 ∪ S2 ∪ S3 ⊆ univ := Finset.subset_univ _
    calc (S1 ∪ S2 ∪ S3).card
        ≤ univ.card := Finset.card_le_card this
      _ = 8 := hU

  -- 包含排斥原理的应用
  -- 对于两个集合：|A ∪ B| = |A| + |B| - |A ∩ B|
  -- 首先处理S1 ∪ S2
  have union_12 : (S1 ∪ S2).card = S1.card + S2.card - (S1 ∩ S2).card := by
    have h' : (S1 ∪ S2).card + (S1 ∩ S2).card = S1.card + S2.card := by
      simpa using (Finset.card_union_add_card_inter S1 S2)
    exact Nat.eq_sub_of_add_eq h'

  -- 然后处理(S1 ∪ S2) ∪ S3
  have union_123 : (S1 ∪ S2 ∪ S3).card = (S1 ∪ S2).card + S3.card - ((S1 ∪ S2) ∩ S3).card := by
    have h' : (S1 ∪ S2 ∪ S3).card + ((S1 ∪ S2) ∩ S3).card = (S1 ∪ S2).card + S3.card := by
      simpa [Finset.union_assoc] using (Finset.card_union_add_card_inter (S1 ∪ S2) S3)
    exact Nat.eq_sub_of_add_eq h'

  -- 展开(S1 ∪ S2) ∩ S3 = (S1 ∩ S3) ∪ (S2 ∩ S3)
  have inter_dist : (S1 ∪ S2) ∩ S3 = (S1 ∩ S3) ∪ (S2 ∩ S3) := by
    ext x
    simp [Finset.mem_inter, Finset.mem_union]
    tauto

  -- 因此|(S1 ∪ S2) ∩ S3| = |S1 ∩ S3| + |S2 ∩ S3| - |S1 ∩ S2 ∩ S3|
  have inter_card : ((S1 ∪ S2) ∩ S3).card = (S1 ∩ S3).card + (S2 ∩ S3).card - (S1 ∩ S2 ∩ S3).card := by
    rw [inter_dist]
    have h' : ((S1 ∩ S3) ∪ (S2 ∩ S3)).card + ((S1 ∩ S3) ∩ (S2 ∩ S3)).card =
        (S1 ∩ S3).card + (S2 ∩ S3).card := by
      simpa using (Finset.card_union_add_card_inter (S1 ∩ S3) (S2 ∩ S3))
    have : (S1 ∩ S3) ∩ (S2 ∩ S3) = S1 ∩ S2 ∩ S3 := by
      ext x
      simp [Finset.mem_inter, and_left_comm, and_assoc, and_comm]
    have h'' : ((S1 ∩ S3) ∪ (S2 ∩ S3)).card + (S1 ∩ S2 ∩ S3).card =
        (S1 ∩ S3).card + (S2 ∩ S3).card := by
      simpa [this] using h'
    exact Nat.eq_sub_of_add_eq h''

  -- 组合所有等式
  have key_eq : (S1 ∪ S2 ∪ S3).card =
      S1.card + S2.card + S3.card - (S1 ∩ S2).card - (S1 ∩ S3).card - (S2 ∩ S3).card + (S1 ∩ S2 ∩ S3).card := by
    nlinarith [union_123, union_12, inter_card]

  -- 从key_eq重排得到交集和的表达式
  have intersection_sum : (S1 ∩ S2).card + (S2 ∩ S3).card + (S3 ∩ S1).card =
      S1.card + S2.card + S3.card - (S1 ∪ S2 ∪ S3).card + (S1 ∩ S2 ∩ S3).card := by
    have : (S3 ∩ S1).card = (S1 ∩ S3).card := by
      congr 1
      ext x
      simp [Finset.mem_inter]
      tauto
    rw [this]
    nlinarith [key_eq]

  -- 应用数值
  calc (S1 ∩ S2).card + (S2 ∩ S3).card + (S3 ∩ S1).card
      = S1.card + S2.card + S3.card - (S1 ∪ S2 ∪ S3).card + (S1 ∩ S2 ∩ S3).card := intersection_sum
    _ = 4 + 4 + 4 - (S1 ∪ S2 ∪ S3).card + (S1 ∩ S2 ∩ S3).card := by rw [h1, h2, h3]
    _ = 12 - (S1 ∪ S2 ∪ S3).card + (S1 ∩ S2 ∩ S3).card := by ring
    _ ≥ 12 - 8 + (S1 ∩ S2 ∩ S3).card := by omega
    _ = 4 + (S1 ∩ S2 ∩ S3).card := by ring
    _ ≥ 4 := by omega

/-- Helper lemma: If a student survives an ordering, they are in getChampions -/
lemma survives_mem_getChampions
    (setup : CompetitionSetup Student Subject)
    (ordering : List Subject)
    (winner : Student)
    (h_perm : ordering.Perm (univ : Finset Subject).toList)
    (h_surv : Survives setup ordering winner) :
    winner ∈ getChampions setup := by
  unfold getChampions
  rw [List.mem_toFinset]

  -- The winner is in the bind of all permutations
  -- We need to show winner ∈ survivors list

  -- Unfold Survives to get the structure
  unfold Survives at h_surv

  -- The ordering must be of the form [s1, s2, s3]
  have h_ord : ∃ s1 s2 s3, ordering = [s1, s2, s3] := by
    cases ordering with
    | nil => cases h_surv
    | cons s1 t =>
      cases t with
      | nil => cases h_surv
      | cons s2 t2 =>
        cases t2 with
        | nil => cases h_surv
        | cons s3 t3 =>
          cases t3 with
          | nil => exact ⟨s1, s2, s3, rfl⟩
          | cons _ _ => cases h_surv
  rcases h_ord with ⟨s1, s2, s3, h_ord⟩
  rw [h_ord] at h_surv
  -- Now h_surv says winner is in the final set S3
  simp at h_surv

  -- Show that [s1, s2, s3] is in the filtered permutations
  -- and winner is in its contribution to the bind

  -- We need to show there exists a permutation p in the filtered list
  -- such that winner is in the contribution from p
  refine (List.mem_flatMap).2 ?_
  refine ⟨[s1, s2, s3], ?_, ?_⟩

  · -- Show [s1, s2, s3] is in the filtered permutations
    apply List.mem_filter.mpr
    constructor
    · -- Show [s1, s2, s3] ∈ (univ : Finset Subject).toList.permutations
      rw [List.mem_permutations]
      -- Use the hypothesis that ordering ~ univ.toList
      rw [← h_ord]
      exact h_perm
    · -- Show [s1, s2, s3].length = 3
      simp

  · -- Show winner is in the contribution from [s1, s2, s3]
    -- The contribution is S3.toList where S3 is the final survivor set
    -- We know winner ∈ S3 from h_surv
    simpa [Finset.mem_toList] using h_surv

/-- Helper lemma: If two different orderings produce the same winner, then count ≤ 5 -/
lemma duplicate_winner_implies_count_le_five
    (setup : CompetitionSetup Student Subject)
    (ord1 ord2 : List Subject)
    (h_diff : ord1 ≠ ord2)
    (h_perm1 : ord1.Perm (univ : Finset Subject).toList)
    (h_perm2 : ord2.Perm (univ : Finset Subject).toList)
    (winner : Student)
    (h_surv1 : Survives setup ord1 winner)
    (h_surv2 : Survives setup ord2 winner) :
    countPotentialChampions setup ≤ 5 := by
  -- The key insight: there are at most 6 orderings (3! = 6)
  -- If two different orderings produce the same winner,
  -- then the set of distinct winners has at most 5 elements
  have h_le_6 := champions_le_six setup
  by_contra h_not_le_5
  push_neg at h_not_le_5
  have h_eq_6 : countPotentialChampions setup = 6 := by omega

  -- If count = 6, then all 6 orderings produce distinct winners
  -- But we have two different orderings producing the same winner

  -- First, show that winner ∈ getChampions
  have h_winner_mem : winner ∈ getChampions setup := by
    apply survives_mem_getChampions setup ord1 winner h_perm1 h_surv1

  -- The key insight: getChampions is constructed by binding over all permutations
  -- If count = 6, then the list before toFinset must have had no duplicates
  -- But winner appears from both ord1 and ord2, so there's a duplicate

  unfold countPotentialChampions getChampions at h_eq_6

  -- The survivors list is created by binding
  let survivors := ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))).flatMap (fun p =>
    match p with
    | [s1', s2', s3'] =>
        let S0 := (univ : Finset Student)
        let S1 := computeTopHalf setup s1' S0
        let S2 := computeTopHalf setup s2' S1
        let S3 := computeTopHalf setup s3' S2
        S3.toList
    | _ => [])

  -- Key fact: there are exactly 6 valid permutations
  have h_six_perms : ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))).length = 6 := by
    have h1 : (univ : Finset Subject).toList.length = 3 := by
      simpa [Finset.length_toList, setup.subject_count]
    have h2 : (univ : Finset Subject).toList.permutations.length = Nat.factorial 3 := by
      rw [List.length_permutations, h1]
    have h3 : ∀ p ∈ (univ : Finset Subject).toList.permutations, p.length = 3 := by
      intro p hp
      have hperm : p.Perm (univ : Finset Subject).toList :=
        (List.mem_permutations.mp hp)
      have hlen := hperm.length_eq
      simpa [h1] using hlen
    have h4 : ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))) =
              (univ : Finset Subject).toList.permutations := by
      apply List.filter_eq_self.mpr
      intro p hp
      have hp' : p.length = 3 := h3 p hp
      simp [hp']
    rw [h4, h2]
    norm_num

  -- The challenge: prove that winner appears at least twice in survivors
  -- This requires showing that ord1 and ord2 both contribute winner to the bind

  -- Strategy: use count_flatMap to show count winner ≥ 2

  -- First, show that ord1 and ord2 are in the filtered permutations
  have h_ord1_mem : ord1 ∈ ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))) := by
    apply List.mem_filter.mpr
    constructor
    · rw [List.mem_permutations]
      exact h_perm1
    ·
      have hlen : ord1.length = (univ : Finset Subject).toList.length :=
        List.Perm.length_eq h_perm1
      have hlen' : ord1.length = 3 := by
        simpa [Finset.length_toList, setup.subject_count] using hlen
      simp [hlen']

  have h_ord2_mem : ord2 ∈ ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))) := by
    apply List.mem_filter.mpr
    constructor
    · rw [List.mem_permutations]
      exact h_perm2
    ·
      have hlen : ord2.length = (univ : Finset Subject).toList.length :=
        List.Perm.length_eq h_perm2
      have hlen' : ord2.length = 3 := by
        simpa [Finset.length_toList, setup.subject_count] using hlen
      simp [hlen']

  -- Now show that winner appears in the contribution from each ordering
  -- This requires matching on the orderings to extract their structure

  -- Key insight: Survives tells us winner is in the final survivor set
  -- We need to connect this to the bind contribution

  -- Extract the structure of ord1
  have h_ord1 : ∃ s1 s2 s3, ord1 = [s1, s2, s3] := by
    have h_len : ord1.length = 3 := by
      have hlen : ord1.length = (univ : Finset Subject).toList.length :=
        List.Perm.length_eq h_perm1
      simpa [Finset.length_toList, setup.subject_count] using hlen
    cases ord1 with
    | nil => simp at h_len
    | cons h1 t1 =>
      cases t1 with
      | nil => simp at h_len
      | cons h2 t2 =>
        cases t2 with
        | nil => simp at h_len
        | cons h3 t3 =>
          cases t3 with
          | nil => exact ⟨h1, h2, h3, rfl⟩
          | cons h4 t4 => simp at h_len
  rcases h_ord1 with ⟨s1, s2, s3, h_ord1_eq⟩

  -- Similarly for ord2
  have h_ord2 : ∃ s1' s2' s3', ord2 = [s1', s2', s3'] := by
    have h_len : ord2.length = 3 := by
      have hlen : ord2.length = (univ : Finset Subject).toList.length :=
        List.Perm.length_eq h_perm2
      simpa [Finset.length_toList, setup.subject_count] using hlen
    cases ord2 with
    | nil => simp at h_len
    | cons h1 t1 =>
      cases t1 with
      | nil => simp at h_len
      | cons h2 t2 =>
        cases t2 with
        | nil => simp at h_len
        | cons h3 t3 =>
          cases t3 with
          | nil => exact ⟨h1, h2, h3, rfl⟩
          | cons h4 t4 => simp at h_len
  rcases h_ord2 with ⟨s1', s2', s3', h_ord2_eq⟩

  -- Now we know ord1 = [s1, s2, s3] and ord2 = [s1', s2', s3']
  -- From Survives, winner is in the final survivor set for each

  rw [h_ord1_eq] at h_surv1
  rw [h_ord2_eq] at h_surv2

  unfold Survives at h_surv1 h_surv2
  simp at h_surv1 h_surv2

  -- h_surv1 and h_surv2 now tell us winner is in the final survivor sets

  -- Show that winner appears in the bind contribution from ord1
  have h_winner_in_ord1_contrib : winner ∈ (match [s1, s2, s3] with
    | [s1', s2', s3'] =>
        let S0 := (univ : Finset Student)
        let S1 := computeTopHalf setup s1' S0
        let S2 := computeTopHalf setup s2' S1
        let S3 := computeTopHalf setup s3' S2
        S3.toList
    | _ => []) := by
    simpa [Finset.mem_toList] using h_surv1

  -- Similarly for ord2
  have h_winner_in_ord2_contrib : winner ∈ (match [s1', s2', s3'] with
    | [s1'', s2'', s3''] =>
        let S0 := (univ : Finset Student)
        let S1 := computeTopHalf setup s1'' S0
        let S2 := computeTopHalf setup s2'' S1
        let S3 := computeTopHalf setup s3'' S2
        S3.toList
    | _ => []) := by
    simpa [Finset.mem_toList] using h_surv2

  -- Now use mem_flatMap to show winner appears in survivors
  rw [← h_ord1_eq] at h_ord1_mem h_winner_in_ord1_contrib
  rw [← h_ord2_eq] at h_ord2_mem h_winner_in_ord2_contrib

  have h_winner_from_ord1 : winner ∈ survivors := by
    apply List.mem_flatMap_of_mem h_ord1_mem
    exact h_winner_in_ord1_contrib

  have h_winner_from_ord2 : winner ∈ survivors := by
    apply List.mem_flatMap_of_mem h_ord2_mem
    exact h_winner_in_ord2_contrib

  -- Now we need to show that these are distinct contributions
  -- i.e., count winner survivors ≥ 2

  -- Use count_flatMap: count winner (l.flatMap f) = sum (map (count winner ∘ f) l)
  have h_count_eq : List.count winner survivors =
      List.sum (List.map (fun p => List.count winner (match p with
        | [s1', s2', s3'] =>
            let S0 := (univ : Finset Student)
            let S1 := computeTopHalf setup s1' S0
            let S2 := computeTopHalf setup s2' S1
            let S3 := computeTopHalf setup s3' S2
            S3.toList
        | _ => [])) ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3)))) := by
    unfold survivors
    exact List.count_flatMap

  -- Now show that count winner ≥ 2
  -- Since ord1 and ord2 are in the list, and winner appears in each contribution,
  -- the sum includes at least two terms that are ≥ 1

  have h_count_ge_2 : List.count winner survivors ≥ 2 := by
    rw [h_count_eq]
    -- The sum includes contributions from ord1 and ord2
    -- Each contribution has count ≥ 1 because winner appears in each

    -- First, show count winner (contribution from ord1) ≥ 1
    have h_count_ord1 : List.count winner (match ord1 with
      | [s1', s2', s3'] =>
          let S0 := (univ : Finset Student)
          let S1 := computeTopHalf setup s1' S0
          let S2 := computeTopHalf setup s2' S1
          let S3 := computeTopHalf setup s3' S2
          S3.toList
      | _ => []) ≥ 1 := by
      rw [h_ord1_eq]
      simp
      have : winner ∈ (let S0 := (univ : Finset Student)
                       let S1 := computeTopHalf setup s1 S0
                       let S2 := computeTopHalf setup s2 S1
                       let S3 := computeTopHalf setup s3 S2
                       S3.toList) := by
        rw [Finset.mem_toList]
        exact h_surv1
      have := List.one_le_count_iff_mem.mpr this
      omega

    -- Similarly for ord2
    have h_count_ord2 : List.count winner (match ord2 with
      | [s1', s2', s3'] =>
          let S0 := (univ : Finset Student)
          let S1 := computeTopHalf setup s1' S0
          let S2 := computeTopHalf setup s2' S1
          let S3 := computeTopHalf setup s3' S2
          S3.toList
      | _ => []) ≥ 1 := by
      rw [h_ord2_eq]
      simp
      have : winner ∈ (let S0 := (univ : Finset Student)
                       let S1 := computeTopHalf setup s1' S0
                       let S2 := computeTopHalf setup s2' S1
                       let S3 := computeTopHalf setup s3' S2
                       S3.toList) := by
        rw [Finset.mem_toList]
        exact h_surv2
      have := List.one_le_count_iff_mem.mpr this
      omega

    -- Now use the fact that ord1 and ord2 are distinct and both in the list
    -- The sum includes both contributions, so sum ≥ 1 + 1 = 2

    -- This requires showing that the contributions add up
    -- Strategy: decompose the sum to isolate the contributions from ord1 and ord2

    -- The sum is over all permutations in the filtered list
    -- We know ord1 and ord2 are in this list
    -- We know the function applied to ord1 gives ≥ 1
    -- We know the function applied to ord2 gives ≥ 1

    -- Use the fact that sum includes all terms
    -- Since ord1 ∈ list, the sum includes the term for ord1
    -- Since ord2 ∈ list, the sum includes the term for ord2
    -- Since ord1 ≠ ord2, these are distinct terms
    -- Therefore sum ≥ (term for ord1) + (term for ord2) ≥ 1 + 1 = 2

    -- Let me try a direct calculation approach
    let f := fun p => List.count winner (match p with
      | [s1', s2', s3'] =>
          let S0 := (univ : Finset Student)
          let S1 := computeTopHalf setup s1' S0
          let S2 := computeTopHalf setup s2' S1
          let S3 := computeTopHalf setup s3' S2
          S3.toList
      | _ => [])

    -- We need to show: (list.map f).sum ≥ 2
    -- We know: ord1 ∈ list, ord2 ∈ list, ord1 ≠ ord2
    -- We know: f ord1 ≥ 1, f ord2 ≥ 1

    -- Key insight: if we can show that f ord1 + f ord2 ≤ (list.map f).sum
    -- then we're done since f ord1 + f ord2 ≥ 1 + 1 = 2

    -- This follows from the fact that ord1 and ord2 are in the list
    -- and the sum includes all terms

    have h_ord1_term : f ord1 ≤ (((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))).map f).sum := by
      apply List.single_le_sum
      · intro x hx
        -- All counts are non-negative
        omega
      · exact h_ord1_mem

    have h_ord2_term : f ord2 ≤ (((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))).map f).sum := by
      apply List.single_le_sum
      · intro x hx
        omega
      · exact h_ord2_mem

    -- But this only gives us that each term is ≤ sum, not that their sum is ≤ sum
    -- We need a different approach

    -- Actually, let me use a more direct argument
    -- The sum equals the sum of all terms
    -- Two of those terms are f ord1 and f ord2
    -- So sum ≥ f ord1 + f ord2 ≥ 1 + 1 = 2

    calc List.sum (List.map f ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))))
        ≥ f ord1 + f ord2 := by
          -- Convert to finset and use Finset.add_le_sum
          -- First, note that the list is the toList of a finset of permutations
          -- We can work with the finset directly

          -- Actually, let's use a direct approach with the list
          -- We know ord1 ∈ list and ord2 ∈ list
          -- We need to show that the sum includes both contributions

          -- Key insight: use the fact that all terms are non-negative
          -- and that the sum includes the terms for ord1 and ord2

          -- Let's use a calculation approach
          let list := ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3)))

          -- The sum over the list equals the sum over the finset
          have h_list_nodup : list.Nodup := by
            apply List.nodup_filter
            exact List.nodup_permutations (Finset.nodup_toList _)

          -- Convert to finset
          have h_sum_eq : (list.map f).sum = (list.toFinset.sum f) := by
            rw [← Finset.sum_toList]
            congr 1
            ext x
            simp [List.mem_toFinset]
            constructor
            · intro hx
              obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
              rw [← hxy]
              exact hy
            · intro hx
              apply List.mem_map_of_mem
              exact hx

          rw [h_sum_eq]

          -- Now use Finset.add_le_sum
          have h_ord1_in_finset : ord1 ∈ list.toFinset := by
            rw [List.mem_toFinset]
            exact h_ord1_mem

          have h_ord2_in_finset : ord2 ∈ list.toFinset := by
            rw [List.mem_toFinset]
            exact h_ord2_mem

          apply Finset.add_le_sum
          · intro x hx
            -- All counts are non-negative
            omega
          · exact h_ord1_in_finset
          · exact h_ord2_in_finset
          · exact h_diff
      _ ≥ 1 + 1 := by
          have : f ord1 ≥ 1 := h_count_ord1
          have : f ord2 ≥ 1 := h_count_ord2
          omega
      _ = 2 := by norm_num

  -- Use duplicate_iff_two_le_count to show winner is a duplicate
  have h_winner_dup : winner ∈+ survivors := by
    rw [List.duplicate_iff_two_le_count]
    exact h_count_ge_2

  -- Therefore survivors is not Nodup
  have h_not_nodup : ¬survivors.Nodup := by
    intro h_nodup
    have := List.nodup_iff_count_le_one.mp h_nodup winner
    omega

  -- By contrapositive of toFinset_card_of_nodup, toFinset.card < survivors.length
  have h_card_lt : survivors.toFinset.card < survivors.length := by
    have h_le := List.toFinset_card_le survivors
    by_contra h_not_lt
    push_neg at h_not_lt
    have h_eq : survivors.toFinset.card = survivors.length := by omega
    have := List.toFinset_card_of_nodup h_not_nodup
    rw [h_eq] at this
    exact absurd this h_not_nodup

  -- But we assumed toFinset.card = 6 and there are 6 permutations
  -- So survivors.length ≤ 6 * (max contribution size)
  -- This gives us a contradiction

  -- Actually, we need to be more careful
  -- We have: survivors.toFinset.card < survivors.length
  -- But survivors.toFinset = getChampions setup (by definition)
  -- And we assumed countPotentialChampions setup = 6
  -- So survivors.toFinset.card = 6

  have h_tofinset_eq : survivors.toFinset = getChampions setup := by
    unfold survivors getChampions
    rfl

  rw [h_tofinset_eq] at h_card_lt
  unfold countPotentialChampions at h_eq_6
  rw [← h_tofinset_eq] at h_eq_6

  -- So we have: 6 < survivors.length
  have : 6 < survivors.length := by
    rw [← h_eq_6]
    exact h_card_lt

  -- But survivors.length ≤ number of permutations * max contribution size
  -- Each permutation contributes at most 2 elements (since final survivor set has card 2)
  -- So survivors.length ≤ 6 * 2 = 12

  -- Actually, this doesn't give us a contradiction directly
  -- The issue is that we need a tighter bound

  -- Let me reconsider: the key is that if count = 6, then each permutation
  -- contributes exactly 1 distinct element
  -- But we've shown that at least one element (winner) appears at least twice
  -- This is the contradiction

  -- Actually, I think the argument should be:
  -- If toFinset.card = 6 and there are 6 permutations,
  -- then each permutation must contribute exactly 1 distinct element
  -- But winner appears in at least 2 contributions
  -- So winner is counted at least twice, meaning toFinset.card < 6
  -- Contradiction!

  omega

/-- 引理：证明上界为5 -/
lemma champions_le_five (setup : CompetitionSetup Student Subject) :
    countPotentialChampions setup ≤ 5 := by
  have h6 := champions_le_six setup

  -- 策略：证明不可能有6个不同的冠军
  -- 使用反证法
  by_contra h_not_le_5
  push_neg at h_not_le_5
  have h_eq_6 : countPotentialChampions setup = 6 := by omega

  -- 如果有6个不同的冠军，则所有6种排列产生不同的冠军

  -- 1. 从Subject中提取三个不同的元素
  obtain ⟨s1, s2, s3, hs12, hs23, hs13, huniv⟩ :=
    exists_three_distinct_of_card_eq_three setup.subject_count

  -- 2. 定义它们的幸存者集合
  let S1 := survivalSet setup s1
  let S2 := survivalSet setup s2
  let S3 := survivalSet setup s3

  -- 3. 应用intersection_lower_bound
  have h_S1_card : S1.card = 4 := survivalSet_card setup s1
  have h_S2_card : S2.card = 4 := survivalSet_card setup s2
  have h_S3_card : S3.card = 4 := survivalSet_card setup s3

  have h_inter_bound : (S1 ∩ S2).card + (S2 ∩ S3).card + (S3 ∩ S1).card ≥ 4 := by
    exact intersection_lower_bound Student setup.student_count S1 S2 S3 h_S1_card h_S2_card h_S3_card

  -- 4. 由exists_intersection_ge_two_of_sum_ge_four，至少存在一个交集大小 ≥ 2
  have h_exists_ge_two : (S1 ∩ S2).card ≥ 2 ∨ (S2 ∩ S3).card ≥ 2 ∨ (S3 ∩ S1).card ≥ 2 := by
    exact exists_intersection_ge_two_of_sum_ge_four S1 S2 S3 h_inter_bound

  -- 5. 案例分析：至少有一个交集大小 ≥ 2
  refine (Or.elim h_exists_ge_two ?h12 ?hrest)
  · intro h12
    -- 情况1：|S1 ∩ S2| ≥ 2
    -- 进一步分析：可能是2, 3, 或4
    by_cases h12_eq_2 : (S1 ∩ S2).card = 2
    · -- |S1 ∩ S2| = 2
      -- 由size_two_intersection_property，存在重复的冠军
      obtain ⟨winner, hw1, hw2⟩ := size_two_intersection_property setup s1 s2 s3 hs12 hs23 hs13 h12_eq_2
      -- 这意味着排列[s1,s2,s3]和[s2,s1,s3]产生相同的冠军
      -- 因此getChampions中至少有一个重复
      -- 由于最多有6种排列，如果有重复，则不同冠军数≤5

      -- 关键：证明countPotentialChampions ≤ 5
      -- getChampions包含所有6种排列的winner
      -- 如果[s1,s2,s3]和[s2,s1,s3]产生相同winner，则最多5个不同元素

      have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
        -- Use the helper lemma with the two orderings [s1,s2,s3] and [s2,s1,s3]
        refine duplicate_winner_implies_count_le_five setup [s1,s2,s3] [s2,s1,s3] ?_ ?_ ?_ winner hw1 hw2
        · -- Prove [s1,s2,s3] ≠ [s2,s1,s3]
          intro h_eq
          injection h_eq with h1 h2
          exact hs12 h1
        · -- Prove [s1,s2,s3] ~ univ.toList
          -- From huniv : univ = {s1, s2, s3}, reduce to the finset {s1,s2,s3}
          have h_s2_notin : s2 ∉ ({s3} : Finset Subject) := by
            simp
            exact hs23
          have h_s1_notin : s1 ∉ (insert s2 {s3} : Finset Subject) := by
            simp
            constructor
            · exact hs12
            · exact hs13
          have h_perm : [s1, s2, s3] ~ ({s1, s2, s3} : Finset Subject).toList := by
            calc [s1, s2, s3]
                = s1 :: s2 :: [s3] := rfl
              _ = s1 :: s2 :: ({s3} : Finset Subject).toList := by rw [Finset.toList_singleton]
              _ ~ s1 :: (insert s2 ({s3} : Finset Subject)).toList := by
                  apply List.Perm.cons
                  exact (Finset.toList_insert h_s2_notin).symm
              _ ~ (insert s1 (insert s2 ({s3} : Finset Subject))).toList := by
                  exact (Finset.toList_insert h_s1_notin).symm
              _ = ({s1, s2, s3} : Finset Subject).toList := rfl
          simpa [huniv] using h_perm
        · -- Prove [s2,s1,s3] ~ univ.toList
          -- Note: {s1, s2, s3} = {s2, s1, s3} (finsets are unordered)
          have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s2, s1, s3} := by
            ext x
            simp [Finset.mem_insert, Finset.mem_singleton, or_left_comm, or_assoc, or_comm]
          have h_s1_notin : s1 ∉ ({s3} : Finset Subject) := by
            simp
            exact hs13
          have h_s2_notin : s2 ∉ (insert s1 {s3} : Finset Subject) := by
            simp
            constructor
            · exact hs12.symm
            · exact hs23
          have h_perm : [s2, s1, s3] ~ ({s1, s2, s3} : Finset Subject).toList := by
            -- First permute to the finset {s2,s1,s3}, then rewrite by h_finset_eq
            have h_perm' : [s2, s1, s3] ~ ({s2, s1, s3} : Finset Subject).toList := by
              calc [s2, s1, s3]
                  = s2 :: s1 :: [s3] := rfl
                _ = s2 :: s1 :: ({s3} : Finset Subject).toList := by rw [Finset.toList_singleton]
                _ ~ s2 :: (insert s1 ({s3} : Finset Subject)).toList := by
                    apply List.Perm.cons
                    exact (Finset.toList_insert h_s1_notin).symm
                _ ~ (insert s2 (insert s1 ({s3} : Finset Subject))).toList := by
                    exact (Finset.toList_insert h_s2_notin).symm
                _ = ({s2, s1, s3} : Finset Subject).toList := rfl
            simpa [h_finset_eq] using h_perm'
          simpa [huniv] using h_perm

      exact (not_le_of_gt h_not_le_5) h_count_le_5
    · -- |S1 ∩ S2| ≥ 3
      have h12_ge_3 : (S1 ∩ S2).card ≥ 3 := by omega
      -- 由于S1和S2的大小都是4，交集大小≥3意味着交集大小是3或4
      by_cases h12_eq_3 : (S1 ∩ S2).card = 3
      · -- |S1 ∩ S2| = 3
        -- According to the solution Case 1, this leads to duplication
        -- Among {w_{s1,s2,s3}, w_{s2,s1,s3}, w_{s2,s3,s1}}, at least two are identical
        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          have h_le_6 := champions_le_six setup
          by_contra h_not_le_5
          push_neg at h_not_le_5
          have h_eq_6 : countPotentialChampions setup = 6 := by omega

          -- Let I = S1 ∩ S2 with |I| = 3
          let I := S1 ∩ S2
          have h_I_card : I.card = 3 := h12_eq_3

          -- 定义 U_12 和 U_21
          let U_12 := computeTopHalf setup s2 S1
          let U_21 := computeTopHalf setup s1 S2

          -- U_12 and U_21 are subsets of I of size 2
          have h_U12_subset_I : U_12 ⊆ I := by
            -- Key: I = S1 ∩ S2, students in I have better s2-scores than students in S1 \ I
            have h_score_comparison : ∀ y ∈ I, ∀ z ∈ S1 \ I, setup.score s2 y > setup.score s2 z := by
              intro y hy z hz
              have hy_S2 : y ∈ S2 := Finset.mem_inter.mp hy |>.2
              have hz_not_S2 : z ∉ S2 := by
                intro hz_S2
                have hz_S1 : z ∈ S1 := Finset.mem_sdiff.mp hz |>.1
                have : z ∈ I := Finset.mem_inter.mpr ⟨hz_S1, hz_S2⟩
                exact Finset.not_mem_sdiff_of_mem this hz
              unfold S2 at hy_S2 hz_not_S2
              have : setup.score s2 y ≥ setup.score s2 z := by
                have hz_univ : z ∈ univ := Finset.mem_univ z
                have hz_diff : z ∈ univ \ survivalSet setup s2 := by
                  rw [Finset.mem_sdiff]
                  exact ⟨hz_univ, hz_not_S2⟩
                unfold survivalSet at hy_S2 hz_diff
                exact computeTopHalf_score_property setup s2 univ y hy_S2 z hz_diff
              by_contra h_not_gt
              push_neg at h_not_gt
              have : setup.score s2 y = setup.score s2 z := by omega
              have h_inj := setup.score_injective s2
              have : y = z := h_inj this
              rw [this] at hy
              have hz_S1 : z ∈ S1 := Finset.mem_sdiff.mp hz |>.1
              have : z ∈ I := hy
              exact Finset.not_mem_sdiff_of_mem this hz
            have h_I_subset_S1 : I ⊆ S1 := Finset.inter_subset_left
            have h_2_le_I : 2 ≤ I.card := by rw [h_I_card]; omega
            unfold U_12
            have h_S1_card : S1.card = 4 := by
              simpa [S1] using (survivalSet_card setup s1)
            simp [computeTopHalf, h_S1_card]
            exact top_k_subset_of_high_scores S1 I (setup.score s2) 2 h_I_subset_S1 h_2_le_I h_score_comparison
          have h_U21_subset_I : U_21 ⊆ I := by
            -- Similar to U_12: students in I have better s1-scores than students in S2 \ I
            have h_score_comparison : ∀ y ∈ I, ∀ z ∈ S2 \ I, setup.score s1 y > setup.score s1 z := by
              intro y hy z hz
              have hy_S1 : y ∈ S1 := Finset.mem_inter.mp hy |>.1
              have hz_not_S1 : z ∉ S1 := by
                intro hz_S1
                have hz_S2 : z ∈ S2 := Finset.mem_sdiff.mp hz |>.1
                have : z ∈ I := Finset.mem_inter.mpr ⟨hz_S1, hz_S2⟩
                exact Finset.not_mem_sdiff_of_mem this hz
              unfold S1 at hy_S1 hz_not_S1
              have : setup.score s1 y ≥ setup.score s1 z := by
                have hz_univ : z ∈ univ := Finset.mem_univ z
                have hz_diff : z ∈ univ \ survivalSet setup s1 := by
                  rw [Finset.mem_sdiff]
                  exact ⟨hz_univ, hz_not_S1⟩
                unfold survivalSet at hy_S1 hz_diff
                exact computeTopHalf_score_property setup s1 univ y hy_S1 z hz_diff
              by_contra h_not_gt
              push_neg at h_not_gt
              have : setup.score s1 y = setup.score s1 z := by omega
              have h_inj := setup.score_injective s1
              have : y = z := h_inj this
              rw [this] at hy
              have hz_S2 : z ∈ S2 := Finset.mem_sdiff.mp hz |>.1
              have : z ∈ I := hy
              exact Finset.not_mem_sdiff_of_mem this hz
            have h_I_subset_S2 : I ⊆ S2 := Finset.inter_subset_right
            have h_2_le_I : 2 ≤ I.card := by rw [h_I_card]; omega
            unfold U_21
            rw [h_S1_eq_S2]
            have h_S2_card : S2.card = 4 := by
              simpa [S2] using (survivalSet_card setup s2)
            simp [computeTopHalf, h_S2_card]
            exact top_k_subset_of_high_scores S2 I (setup.score s1) 2 h_I_subset_S2 h_2_le_I h_score_comparison
          -- We'll show that at least two of the three orderings produce the same winner
          -- The 3 orderings are: [s1,s2,s3], [s2,s1,s3], [s2,s3,s1]

          -- Key insight: U_12 ⊆ I and U_21 ⊆ I, both have size 2, and |I| = 3
          have h_S1_card : S1.card = 4 := by
            simpa [S1] using (survivalSet_card setup s1)
          have h_U12_card : U_12.card = 2 := by
            unfold U_12
            simpa [h_S1_card] using (computeTopHalf_card setup s2 S1)
          have h_U21_card : U_21.card = 2 := by
            unfold U_21
            rw [h_S1_eq_S2]
            have h_S2_card : S2.card = 4 := by
              simpa [S2] using (survivalSet_card setup s2)
            simpa [h_S2_card] using (computeTopHalf_card setup s1 S2)

          -- Since U_12 ⊆ I and |U_12| = 2 and |I| = 3, there exists an element in I \ U_12
          have h_exists_not_U12 : ∃ x ∈ I, x ∉ U_12 := by
            by_contra h_not
            push_neg at h_not
            have : I ⊆ U_12 := h_not
            have : I.card ≤ U_12.card := Finset.card_le_card this
            rw [h_I_card, h_U12_card] at this
            omega

          -- Similarly for U_21
          have h_exists_not_U21 : ∃ x ∈ I, x ∉ U_21 := by
            by_contra h_not
            push_neg at h_not
            have : I ⊆ U_21 := h_not
            have : I.card ≤ U_21.card := Finset.card_le_card this
            rw [h_I_card, h_U21_card] at this
            omega

          -- Consider U_23 = computeTopHalf s3 S2
          let U_23 := computeTopHalf setup s3 S2
          have h_S2_card : S2.card = 4 := by
            simpa [S2] using (survivalSet_card setup s2)
          have h_U23_card : U_23.card = 2 := by
            simpa [h_S2_card] using (computeTopHalf_card setup s3 S2)

          -- The winners are:
          -- w_{s1,s2,s3} ∈ computeTopHalf s3 U_12
          -- w_{s2,s1,s3} ∈ computeTopHalf s3 U_21
          -- w_{s2,s3,s1} ∈ computeTopHalf s1 U_23

          -- Since |U_12| = |U_21| = 2 and both are subsets of I (size 3),
          -- and they're selected by different criteria (s2 vs s1),
          -- they might overlap or be disjoint

          -- Key observation: If U_12 = U_21, then the first two orderings produce the same winner
          by_cases h_U12_eq_U21 : U_12 = U_21
          · -- U_12 = U_21, so w_{s1,s2,s3} = w_{s2,s1,s3}
            have h_dup : ∃ winner, Survives setup [s1, s2, s3] winner ∧ Survives setup [s2, s1, s3] winner := by
              have h_surv1 : ∃ w, Survives setup [s1, s2, s3] w := survives_exists setup [s1, s2, s3] (by decide)
              obtain ⟨w, hw⟩ := h_surv1
              use w
              constructor
              · exact hw
              · -- w ∈ computeTopHalf s3 U_21 (since U_12 = U_21)
                unfold Survives at hw ⊢
                simp [h_U12_eq_U21] at hw ⊢
                exact hw
            obtain ⟨winner, hw1, hw2⟩ := h_dup
            have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
              refine duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s2, s1, s3] ?_ ?_ ?_ winner hw1 hw2
              · intro h_eq
                injection h_eq with h1 h_rest
                injection h_rest
              · decide
              · decide
            omega
          · -- U_12 ≠ U_21
            -- Following the mathematical solution's approach
            -- Find x = the student in I with the best s3-score
            have h_I_nonempty : I.Nonempty := by
              rw [Finset.card_pos]
              rw [h_I_card]
              omega

            -- Use Finset.exists_max_image to find the best s3-scorer
            have h_exists_best : ∃ x ∈ I, ∀ z ∈ I, setup.score s3 z ≤ setup.score s3 x := by
              exact Finset.exists_max_image I (setup.score s3) h_I_nonempty

            obtain ⟨x, hx_I, hx_best⟩ := h_exists_best

            -- Show that x ∈ U_23 (top 2 s3-scorers in S2)
            have h_I_subset_S2 : I ⊆ S2 := Finset.inter_subset_right

            have hx_in_U23 : x ∈ U_23 := by
              unfold U_23
              -- x is the best s3-scorer in I (size 3)
              -- I ⊆ S2 and |S2| = 4, so S2 has at most 1 student outside I
              -- Even if that student has better s3-score, x is still in top 2 of S2
              -- because x beats the other 2 elements of I

              -- We need to show x is in the top 2 s3-scorers of S2
              -- Strategy: Show that at most 1 student in S2 has better s3-score than x

              -- Let's use a counting argument
              -- |{y ∈ S2 | score s3 y > score s3 x}| ≤ 1
              have h_better_count : (S2.filter (fun y => setup.score s3 y > setup.score s3 x)).card ≤ 1 := by
                -- Students in I \ {x} have score ≤ x
                have h_I_minus_x : ∀ y ∈ I, y ≠ x → setup.score s3 y ≤ setup.score s3 x := by
                  intro y hy hne
                  have := hx_best y hy
                  exact this

                -- So students with better score must be in S2 \ I
                have h_better_in_diff : S2.filter (fun y => setup.score s3 y > setup.score s3 x) ⊆ S2 \ I := by
                  intro y hy
                  rw [Finset.mem_filter] at hy
                  rw [Finset.mem_sdiff]
                  constructor
                  · exact hy.1
                  · intro hy_I
                    have : setup.score s3 y ≤ setup.score s3 x := hx_best y hy_I
                    omega

                -- |S2 \ I| ≤ |S2| - |I| = 4 - 3 = 1
                have h_diff_card : (S2 \ I).card ≤ 1 := by
                  have : (S2 \ I).card = S2.card - I.card := by
                    rw [Finset.card_sdiff h_I_subset_S2]
                  rw [this, h_S2_card, h_I_card]
                  omega

                have := Finset.card_le_card h_better_in_diff
                omega

              -- Therefore x is in top 2
              -- We've shown that at most 1 student in S2 has better s3-score than x
              -- So x is among the top 2 s3-scorers in S2
              -- Therefore x ∈ computeTopHalf s3 S2 = U_23

              -- Strategy: Show that x is not in the bottom |S2| - 2 = 2 students
              -- Equivalently, show that at most 1 student has better score than x

              -- We need to use the fact that computeTopHalf selects the top k elements
              -- and we've shown at most 1 element has better score than x

              -- Use a counting argument:
              -- |{y ∈ S2 | score y > score x}| ≤ 1
              -- So x is in position ≤ 2 in the sorted order
              -- Therefore x ∈ top 2 = computeTopHalf s3 S2

              -- This requires a lemma about computeTopHalf and ranking
              -- Use at_most_k_minus_1_better_implies_in_top_k
              have hx_in_S2 : x ∈ S2 := h_I_subset_S2 hx_I
              apply at_most_k_minus_1_better_implies_in_top_k setup s3 S2 x 2
              · exact hx_in_S2
              · omega
              · rw [h_S2_card]; omega
              · exact h_better_count

            -- Case analysis on whether w_{s2,s3,s1} = x
            have h_w231_exists : ∃ w, Survives setup [s2, s3, s1] w := survives_exists setup [s2, s3, s1] (by decide)
            obtain ⟨w_231, hw_231⟩ := h_w231_exists

            by_cases h_w231_eq_x : w_231 = x
            · -- Case: w_{s2,s3,s1} = x
              -- Show that at least one of w_{s1,s2,s3} or w_{s2,s1,s3} also equals x
              -- If neither equals x, then x ∉ U_12 and x ∉ U_21
              -- But U_12 and U_21 are size-2 subsets of I (size 3)
              -- So U_12 = I \ {x} and U_21 = I \ {x}
              -- Therefore U_12 = U_21, which means w_{s1,s2,s3} = w_{s2,s1,s3} (duplicate)

              have h_w123_exists : ∃ w, Survives setup [s1, s2, s3] w := survives_exists setup [s1, s2, s3] (by decide)
              obtain ⟨w_123, hw_123⟩ := h_w123_exists

              have h_w213_exists : ∃ w, Survives setup [s2, s1, s3] w := survives_exists setup [s2, s1, s3] (by decide)
              obtain ⟨w_213, hw_213⟩ := h_w213_exists

              -- If w_123 = x or w_213 = x, we have a duplicate with w_231 = x
              by_cases h_w123_eq_x : w_123 = x
              · -- w_123 = x and w_231 = x, duplicate!
                have h_dup : ∃ winner, Survives setup [s1, s2, s3] winner ∧ Survives setup [s2, s3, s1] winner := by
                  use x
                  constructor
                  · rw [← h_w123_eq_x]; exact hw_123
                  · rw [← h_w231_eq_x]; exact hw_231
                obtain ⟨winner, hw1, hw2⟩ := h_dup
                have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                  apply duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s2, s3, s1]
                  · intro h_eq
                    injection h_eq with h1 h_rest
                    injection h_rest with h2
                    injection h2
                  · decide
                  · decide
                  · exact hw1
                  · exact hw2
                omega

              · by_cases h_w213_eq_x : w_213 = x
                · -- w_213 = x and w_231 = x, duplicate!
                  have h_dup : ∃ winner, Survives setup [s2, s1, s3] winner ∧ Survives setup [s2, s3, s1] winner := by
                    use x
                    constructor
                    · rw [← h_w213_eq_x]; exact hw_213
                    · rw [← h_w231_eq_x]; exact hw_231
                  obtain ⟨winner, hw1, hw2⟩ := h_dup
                  have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                    apply duplicate_winner_implies_count_le_five setup [s2, s1, s3] [s2, s3, s1]
                    · intro h_eq
                      injection h_eq with h1 h_rest
                      injection h_rest with h2
                      injection h2
                    · decide
                    · decide
                    · exact hw1
                    · exact hw2
                  omega

                · -- Neither w_123 nor w_213 equals x
                  -- Then x ∉ U_12 and x ∉ U_21
                  have hx_not_U12 : x ∉ U_12 := by
                    intro hx_U12
                    -- w_123 is selected from U_12 by taking best s3-scorer
                    -- If x ∈ U_12 and x is best s3-scorer in I, and U_12 ⊆ I,
                    -- then x must be best s3-scorer in U_12, so w_123 = x
                    unfold Survives at hw_123
                    simp only [List.foldl_cons, List.foldl_nil] at hw_123
                    -- hw_123 : w_123 ∈ computeTopHalf s3 U_12
                    -- Need to show w_123 = x

                    -- x is best s3-scorer in U_12
                    have hx_best_U12 : ∀ y ∈ U_12, setup.score s3 y ≤ setup.score s3 x := by
                      intro y hy
                      have hy_I : y ∈ I := h_U12_subset_I hy
                      exact hx_best y hy_I

                    -- computeTopHalf s3 U_12 has size 1
                    have h_top_card : (computeTopHalf setup s3 U_12).card = 1 := by
                      rw [computeTopHalf_card, h_U12_card]
                      norm_num

                    -- x ∈ computeTopHalf s3 U_12 (since x is best)
                    have hx_in_top : x ∈ computeTopHalf setup s3 U_12 := by
                      -- Use max_score_in_computeTopHalf lemma
                      apply max_score_in_computeTopHalf setup s3 U_12 x 1
                      · exact hx_U12
                      · exact hx_best_U12
                      · omega
                      · rw [h_U12_card]; omega

                    -- Since |computeTopHalf s3 U_12| = 1 and both x and w_123 are in it, x = w_123
                    have : computeTopHalf setup s3 U_12 = {x} := by
                      have : (computeTopHalf setup s3 U_12).card = 1 := h_top_card
                      exact Finset.card_eq_one.mp this |>.choose_spec |> fun h =>
                        Finset.eq_singleton_iff_unique_mem.mpr ⟨hx_in_top, fun y hy =>
                          if h_eq : y = x then h_eq else by
                            -- If y ≠ x and y ∈ computeTopHalf, contradiction with size 1
                            have : {x, y}.card ≤ (computeTopHalf setup s3 U_12).card := by
                              apply Finset.card_le_card
                              intro z hz
                              rw [Finset.mem_insert, Finset.mem_singleton] at hz
                              cases hz with
                              | inl h => rw [h]; exact hx_in_top
                              | inr h => rw [h]; exact hy
                            rw [h_top_card] at this
                            have : {x, y}.card = 2 := by
                              rw [Finset.card_insert_of_not_mem]
                              · simp
                              · rw [Finset.mem_singleton]
                                exact h_eq
                            omega⟩
                    rw [this] at hw_123
                    rw [Finset.mem_singleton] at hw_123
                    exact h_w123_eq_x hw_123

                  have hx_not_U21 : x ∉ U_21 := by
                    intro hx_U21
                    -- Symmetric to the U_12 case
                    unfold Survives at hw_213
                    simp only [List.foldl_cons, List.foldl_nil] at hw_213

                    -- x is best s3-scorer in U_21
                    have hx_best_U21 : ∀ y ∈ U_21, setup.score s3 y ≤ setup.score s3 x := by
                      intro y hy
                      have hy_I : y ∈ I := h_U21_subset_I hy
                      exact hx_best y hy_I

                    -- computeTopHalf s3 U_21 has size 1
                    have h_top_card : (computeTopHalf setup s3 U_21).card = 1 := by
                      rw [computeTopHalf_card, h_U21_card]
                      norm_num

                    -- x ∈ computeTopHalf s3 U_21
                    have hx_in_top : x ∈ computeTopHalf setup s3 U_21 := by
                      -- Use max_score_in_computeTopHalf lemma
                      apply max_score_in_computeTopHalf setup s3 U_21 x 1
                      · exact hx_U21
                      · exact hx_best_U21
                      · omega
                      · rw [h_U21_card]; omega

                    -- Since |computeTopHalf s3 U_21| = 1 and both x and w_213 are in it, x = w_213
                    have : computeTopHalf setup s3 U_21 = {x} := by
                      exact Finset.card_eq_one.mp h_top_card |>.choose_spec |> fun h =>
                        Finset.eq_singleton_iff_unique_mem.mpr ⟨hx_in_top, fun y hy =>
                          if h_eq : y = x then h_eq else by
                            have : {x, y}.card ≤ (computeTopHalf setup s3 U_21).card := by
                              apply Finset.card_le_card
                              intro z hz
                              rw [Finset.mem_insert, Finset.mem_singleton] at hz
                              cases hz with
                              | inl h => rw [h]; exact hx_in_top
                              | inr h => rw [h]; exact hy
                            rw [h_top_card] at this
                            have : {x, y}.card = 2 := by
                              rw [Finset.card_insert_of_not_mem]
                              · simp
                              · rw [Finset.mem_singleton]
                                exact h_eq
                            omega⟩
                    rw [this] at hw_213
                    rw [Finset.mem_singleton] at hw_213
                    exact h_w213_eq_x hw_213

                  -- Since U_12 ⊆ I, |U_12| = 2, |I| = 3, and x ∉ U_12, we have U_12 = I \ {x}
                  have h_U12_eq : U_12 = I \ {x} := by
                    -- U_12 ⊆ I \ {x}
                    have h_sub : U_12 ⊆ I \ {x} := by
                      intro y hy
                      rw [Finset.mem_sdiff]
                      constructor
                      · exact h_U12_subset_I hy
                      · rw [Finset.mem_singleton]
                        intro h_eq
                        rw [h_eq] at hy
                        exact hx_not_U12 hy
                    -- |I \ {x}| = |I| - 1 = 3 - 1 = 2
                    have h_diff_card : (I \ {x}).card = 2 := by
                      have hx_in_I : x ∈ I := hx_I
                      have : (I \ {x}).card = I.card - 1 := by
                        rw [Finset.card_sdiff]
                        · simp [Finset.card_singleton]
                        · exact Finset.singleton_subset_iff.mpr hx_in_I
                      rw [this, h_I_card]
                      omega
                    -- |U_12| = 2 = |I \ {x}|, so U_12 = I \ {x}
                    exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_U12_card, h_diff_card])

                  -- Similarly U_21 = I \ {x}
                  have h_U21_eq : U_21 = I \ {x} := by
                    -- U_21 ⊆ I \ {x}
                    have h_sub : U_21 ⊆ I \ {x} := by
                      intro y hy
                      rw [Finset.mem_sdiff]
                      constructor
                      · exact h_U21_subset_I hy
                      · rw [Finset.mem_singleton]
                        intro h_eq
                        rw [h_eq] at hy
                        exact hx_not_U21 hy
                    -- |I \ {x}| = 2
                    have h_diff_card : (I \ {x}).card = 2 := by
                      have hx_in_I : x ∈ I := hx_I
                      have : (I \ {x}).card = I.card - 1 := by
                        rw [Finset.card_sdiff]
                        · simp [Finset.card_singleton]
                        · exact Finset.singleton_subset_iff.mpr hx_in_I
                      rw [this, h_I_card]
                      omega
                    -- |U_21| = 2 = |I \ {x}|, so U_21 = I \ {x}
                    exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_U21_card, h_diff_card])

                  -- Therefore U_12 = U_21
                  have h_U12_eq_U21_contra : U_12 = U_21 := by
                    rw [h_U12_eq, h_U21_eq]

                  -- But we assumed U_12 ≠ U_21, contradiction!
                  exact h_U12_eq_U21 h_U12_eq_U21_contra

            · -- Case: w_{s2,s3,s1} ≠ x
              -- Then w_{s2,s3,s1} is another student in U_23
              -- Since |U_23| = 2 and x ∈ U_23, we have U_23 = {x, y} for some y ≠ x
              -- w_{s2,s3,s1} is selected from U_23 by taking best s1-scorer
              -- If w_{s2,s3,s1} ≠ x, then w_{s2,s3,s1} = y

              -- Get the second element of U_23
              have h_U23_card : U_23.card = 2 := computeTopHalf_card setup s3 S2

              -- U_23 = {x, y} for some y
              have h_exists_y : ∃ y ∈ U_23, y ≠ x := by
                -- Since |U_23| = 2 and x ∈ U_23, there exists another element
                by_contra h_not
                push_neg at h_not
                -- If no other element, then U_23 = {x}
                have : U_23 = {x} := by
                  ext z
                  constructor
                  · intro hz
                    rw [Finset.mem_singleton]
                    by_cases h_eq : z = x
                    · exact h_eq
                    · have := h_not z hz
                      exact absurd h_eq this
                  · intro hz
                    rw [Finset.mem_singleton] at hz
                    rw [hz]
                    exact hx_in_U23
                have : U_23.card = 1 := by
                  rw [this]
                  simp
                rw [h_U23_card] at this
                omega

              obtain ⟨y, hy_U23, hy_ne_x⟩ := h_exists_y

              -- y is the second-best s3-scorer in I
              -- (since U_23 contains top 2 s3-scorers from S2, and x is best in I)

              -- w_{s2,s3,s1} = y (since w_{s2,s3,s1} ≠ x and w_{s2,s3,s1} ∈ U_23)
              have h_w231_eq_y : w_231 = y := by
                -- w_231 ∈ computeTopHalf s1 U_23
                unfold Survives at hw_231
                simp only [List.foldl_cons, List.foldl_nil] at hw_231
                -- hw_231 : w_231 ∈ computeTopHalf s1 U_23

                -- computeTopHalf s1 U_23 has size 1
                have h_top_card : (computeTopHalf setup s1 U_23).card = 1 := by
                  rw [computeTopHalf_card, h_U23_card]
                  norm_num

                -- w_231 ∈ U_23 (since computeTopHalf s1 U_23 ⊆ U_23)
                have hw_231_U23 : w_231 ∈ U_23 := by
                  have : computeTopHalf setup s1 U_23 ⊆ U_23 := by
                    unfold computeTopHalf
                    intro z hz
                    rw [Finset.mem_toFinset] at hz
                    have : z ∈ U_23.toList.mergeSort (fun a b => setup.score s1 a > setup.score s1 b) := by
                      exact List.mem_of_mem_take hz
                    rw [List.mem_mergeSort] at this
                    rw [← Finset.mem_toList]
                    exact this
                  exact this hw_231

                -- U_23 = {x, y}, so w_231 ∈ {x, y}
                have : w_231 = x ∨ w_231 = y := by
                  -- Need to show U_23 = {x, y}
                  have h_U23_eq : U_23 = {x, y} := by
                    ext z
                    constructor
                    · intro hz
                      rw [Finset.mem_insert, Finset.mem_singleton]
                      by_cases h_eq_x : z = x
                      · left; exact h_eq_x
                      · right
                        -- z ∈ U_23 and z ≠ x, so z = y
                        by_cases h_eq_y : z = y
                        · exact h_eq_y
                        · -- z ≠ x and z ≠ y, but |U_23| = 2 and {x, y} ⊆ U_23
                          -- So U_23 has at least 3 elements, contradiction
                          have : {x, y, z}.card ≤ U_23.card := by
                            apply Finset.card_le_card
                            intro w hw
                            rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hw
                            cases hw with
                            | inl h => rw [h]; exact hx_in_U23
                            | inr h => cases h with
                              | inl h => rw [h]; exact hy_U23
                              | inr h => rw [h]; exact hz
                          have : {x, y, z}.card = 3 := by
                            rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem]
                            · simp
                            · rw [Finset.mem_singleton]; exact h_eq_y
                            · rw [Finset.mem_insert, Finset.mem_singleton]
                              push_neg
                              exact ⟨h_eq_x, h_eq_y⟩
                          rw [this, h_U23_card] at this
                          omega
                    · intro hz
                      rw [Finset.mem_insert, Finset.mem_singleton] at hz
                      cases hz with
                      | inl h => rw [h]; exact hx_in_U23
                      | inr h => rw [h]; exact hy_U23
                  rw [h_U23_eq] at hw_231_U23
                  rw [Finset.mem_insert, Finset.mem_singleton] at hw_231_U23
                  exact hw_231_U23

                cases this with
                | inl h => exact absurd h h_w231_eq_x
                | inr h => exact h

              -- Now we need to show that y also appears as one of w_{s1,s2,s3} or w_{s2,s1,s3}
              -- This would give us a duplicate

              -- Key insight: y ∈ I and |I| = 3, so I = {x, y, z} for some z
              -- U_12 and U_21 are size-2 subsets of I
              -- So at least one of them contains y

              -- Since I has 3 elements and U_12 has 2 elements, either x ∈ U_12 or y ∈ U_12 (or both)
              -- Similarly for U_21

              have hy_I : y ∈ I := by
                have : y ∈ U_23 := hy_U23
                have : U_23 ⊆ S2 := by
                  unfold U_23
                  unfold computeTopHalf
                  intro z hz
                  rw [Finset.mem_toFinset] at hz
                  have : z ∈ S2.toList.mergeSort (fun a b => setup.score s3 a > setup.score s3 b) := by
                    exact List.mem_of_mem_take hz
                  rw [List.mem_mergeSort] at this
                  rw [← Finset.mem_toList]
                  exact this
                have hy_S2 : y ∈ S2 := this hy_U23
                -- y ∈ S2 and y ∈ I requires y ∈ S1 (since I = S1 ∩ S2)
                -- Actually, we need to show y ∈ S1
                -- We know U_23 ⊆ S2 and x, y ∈ U_23
                -- We also know x ∈ I = S1 ∩ S2
                -- For y, we need to check if y ∈ S1

                -- Actually, let me use a different approach
                -- We know I = S1 ∩ S2 and |I| = 3
                -- We know x ∈ I (proven earlier)
                -- We know U_23 is top 2 s3-scorers in S2
                -- We know x is best s3-scorer in I

                -- Since x and y are both in U_23 (top 2 in S2), and x is best in I,
                -- y must be in I as well (otherwise there would be 3 elements in I with better s3-scores than some element in S2 \ I)

                -- For now, let me try a direct approach
                -- We need to show y ∈ S1
                -- We know y ∈ S2 (proven above)
                -- So we need y ∈ S1 to get y ∈ I = S1 ∩ S2

                -- Key observation: U_23 = top 2 s3-scorers in S2
                -- We have x, y ∈ U_23 with x ≠ y
                -- We know x ∈ I and x is best s3-scorer in I

                -- If y ∉ I, then y ∈ S2 \ I
                -- Since |I| = 3 and x ∈ I, there are 2 other elements in I
                -- These 2 elements are not in U_23 (since U_23 = {x, y} and y ∉ I)
                -- So these 2 elements have worse s3-scores than y

                -- But we also know x is the best s3-scorer in I
                -- So these 2 elements have worse s3-scores than x
                -- This means: score x > score (2 elements in I) and score y > score (2 elements in I)

                -- Now, |S2| = 4 and |I| = 3, so |S2 \ I| = 1
                -- If y ∈ S2 \ I, then S2 \ I = {y}
                -- So S2 = I ∪ {y} = {x, a, b, y} where a, b are the other 2 elements in I

                -- But then U_23 (top 2 in S2) = {x, y} means a, b have worse s3-scores than both x and y
                -- This is consistent, so we can't derive a contradiction this way

                -- Let me try using the fact that U_23 ⊆ I (which we need to prove)
                -- Actually, we haven't proven U_23 ⊆ I yet

                -- Alternative: use the structure of the problem
                -- We're in the case where |S1 ∩ S2| = 3
                -- The mathematical solution says to find the best s3-scorer in I
                -- and show it's in U_23

                -- For now, accept this and move forward
                -- The key is that y should be the second-best s3-scorer in I
                have hy_I : y ∈ I := by
                  -- We'll prove this by showing y ∈ S1
                  -- Since y ∈ S2 (proven above), this gives y ∈ I = S1 ∩ S2
                  rw [Finset.mem_inter]
                  constructor
                  · -- Need to show y ∈ S1
                    -- Proof by contradiction: if y ∉ S1, then w_231 = x
                    by_contra hy_not_S1
                    -- If y ∉ S1, then y is not in top half for s1
                    -- Since x ∈ I ⊆ S1, x is in top half for s1
                    -- So x has better s1-score than y
                    have hx_S1 : x ∈ S1 := Finset.mem_inter.mp hx_I |>.1
                    unfold S1 at hx_S1 hy_not_S1
                    -- x ∈ survivalSet s1 and y ∉ survivalSet s1
                    -- This means score s1 x > score s1 y
                    have h_score_x_gt_y : setup.score s1 x > setup.score s1 y := by
                      have hy_univ : y ∈ univ := Finset.mem_univ y
                      have hy_diff : y ∈ univ \ survivalSet setup s1 := by
                        rw [Finset.mem_sdiff]
                        exact ⟨hy_univ, hy_not_S1⟩
                      unfold survivalSet at hx_S1 hy_diff
                      have : setup.score s1 x ≥ setup.score s1 y :=
                        computeTopHalf_score_property setup s1 univ x hx_S1 y hy_diff
                      by_contra h_not_gt
                      push_neg at h_not_gt
                      have : setup.score s1 x = setup.score s1 y := by omega
                      have h_inj := setup.score_injective s1
                      have : x = y := h_inj this
                      exact hy_ne_x (this.symm)

                    -- Now, w_231 is selected from U_23 = {x, y} by best s1-scorer
                    -- Since x has better s1-score than y, w_231 = x
                    have h_w231_eq_x_contra : w_231 = x := by
                      -- w_231 ∈ computeTopHalf s1 U_23
                      unfold Survives at hw_231
                      simp only [List.foldl_cons, List.foldl_nil] at hw_231
                      -- hw_231 : w_231 ∈ computeTopHalf s1 U_23

                      -- computeTopHalf s1 U_23 selects the best s1-scorer from U_23 = {x, y}
                      -- Since x has better s1-score than y, it selects x
                      have h_U23_eq : U_23 = {x, y} := h_U23_eq

                      -- Show that x is the unique best s1-scorer in U_23
                      have hx_best_s1_U23 : ∀ z ∈ U_23, setup.score s1 z ≤ setup.score s1 x := by
                        intro z hz
                        rw [h_U23_eq] at hz
                        rw [Finset.mem_insert, Finset.mem_singleton] at hz
                        cases hz with
                        | inl h => rw [h]
                        | inr h => rw [h]; omega

                      -- computeTopHalf s1 U_23 has size 1
                      have h_top_card : (computeTopHalf setup s1 U_23).card = 1 := by
                        rw [computeTopHalf_card, h_U23_card]
                        norm_num

                      -- x ∈ computeTopHalf s1 U_23 (since x has max s1-score in U_23)
                      have hx_in_top : x ∈ computeTopHalf setup s1 U_23 := by
                        have hx_in_U23 : x ∈ U_23 := by rw [h_U23_eq]; simp
                        apply max_score_in_computeTopHalf setup s1 U_23 x 1
                        · exact hx_in_U23
                        · exact hx_best_s1_U23
                        · omega
                        · rw [h_U23_card]; omega

                      -- Since |computeTopHalf s1 U_23| = 1 and both x and w_231 are in it, x = w_231
                      have h_singleton : ∃ a, computeTopHalf setup s1 U_23 = {a} := Finset.card_eq_one.mp h_top_card
                      obtain ⟨a, ha⟩ := h_singleton
                      rw [ha] at hx_in_top hw_231
                      rw [Finset.mem_singleton] at hx_in_top hw_231
                      rw [← hx_in_top, hw_231]

                    -- But this contradicts our assumption that w_231 ≠ x
                    exact h_w231_eq_x h_w231_eq_x_contra
                  · exact hy_S2

              -- Now, since |I| = 3 and I = {x, y, z} for some z, and U_12 ⊆ I with |U_12| = 2,
              -- we have either U_12 = {x, y} or U_12 = {x, z} or U_12 = {y, z}

              by_cases hy_U12 : y ∈ U_12
              · -- y ∈ U_12, so y might be w_{s1,s2,s3}
                -- w_{s1,s2,s3} is the best s3-scorer in U_12
                -- If y is the best s3-scorer in U_12, then w_{s1,s2,s3} = y (duplicate with w_231 = y)

                by_cases h_y_best_U12 : y ∈ computeTopHalf setup s3 U_12
                · -- y is selected from U_12, so w_{s1,s2,s3} = y
                  have h_w123_exists : ∃ w, Survives setup [s1, s2, s3] w := survives_exists setup [s1, s2, s3] (by decide)
                  obtain ⟨w_123, hw_123⟩ := h_w123_exists

                  -- w_123 ∈ computeTopHalf s3 U_12
                  have hw_123_top : w_123 ∈ computeTopHalf setup s3 U_12 := by
                    unfold Survives at hw_123
                    simp only [List.foldl_cons, List.foldl_nil] at hw_123
                    exact hw_123

                  -- Since |computeTopHalf s3 U_12| = 1 and both y and w_123 are in it, y = w_123
                  have h_top_card : (computeTopHalf setup s3 U_12).card = 1 := by
                    rw [computeTopHalf_card, h_U12_card]
                    norm_num

                  have : computeTopHalf setup s3 U_12 = {y} := by
                    -- Use Finset.card_eq_one to show it's a singleton
                    have h_singleton : ∃ a, computeTopHalf setup s3 U_12 = {a} := Finset.card_eq_one.mp h_top_card
                    obtain ⟨a, ha⟩ := h_singleton
                    -- Since y ∈ computeTopHalf s3 U_12 and it's a singleton {a}, we have y = a
                    rw [ha] at h_y_best_U12
                    rw [Finset.mem_singleton] at h_y_best_U12
                    rw [← h_y_best_U12]
                    exact ha

                  rw [this] at hw_123_top
                  rw [Finset.mem_singleton] at hw_123_top
                  have h_w123_eq_y : w_123 = y := hw_123_top

                  -- So w_123 = y and w_231 = y, duplicate!
                  have h_dup : ∃ winner, Survives setup [s1, s2, s3] winner ∧ Survives setup [s2, s3, s1] winner := by
                    use y
                    constructor
                    · rw [← h_w123_eq_y]; exact hw_123
                    · rw [← h_w231_eq_y]; exact hw_231

                  obtain ⟨winner, hw1, hw2⟩ := h_dup
                  have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                    apply duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s2, s3, s1]
                    · intro h_eq
                      injection h_eq with h1 h_rest
                      injection h_rest with h2
                      injection h2
                    · decide
                    · decide
                    · exact hw1
                    · exact hw2
                  omega

                · -- y is not selected from U_12, so someone else is selected
                  -- w_123 is the best s3-scorer in U_12
                  -- Since y ∈ U_12 but y ∉ computeTopHalf s3 U_12, w_123 ≠ y

                  have h_w123_exists : ∃ w, Survives setup [s1, s2, s3] w := survives_exists setup [s1, s2, s3] (by decide)
                  obtain ⟨w_123, hw_123⟩ := h_w123_exists

                  -- w_123 ∈ computeTopHalf s3 U_12
                  have hw_123_top : w_123 ∈ computeTopHalf setup s3 U_12 := by
                    unfold Survives at hw_123
                    simp only [List.foldl_cons, List.foldl_nil] at hw_123
                    exact hw_123

                  -- w_123 ∈ U_12 ⊆ I
                  have hw_123_I : w_123 ∈ I := by
                    have : computeTopHalf setup s3 U_12 ⊆ U_12 := by
                      unfold computeTopHalf
                      intro z hz
                      rw [Finset.mem_toFinset] at hz
                      have : z ∈ U_12.toList.mergeSort (fun a b => setup.score s3 a > setup.score s3 b) := by
                        exact List.mem_of_mem_take hz
                      rw [List.mem_mergeSort] at this
                      rw [← Finset.mem_toList]
                      exact this
                    have hw_123_U12 : w_123 ∈ U_12 := this hw_123_top
                    exact h_U12_subset_I hw_123_U12

                  -- w_123 ≠ y (since y ∉ computeTopHalf s3 U_12)
                  have hw_123_ne_y : w_123 ≠ y := by
                    intro h_eq
                    rw [h_eq] at hw_123_top
                    exact h_y_best_U12 hw_123_top

                  -- I = {x, y, z} for some z, so w_123 ∈ {x, z}
                  -- Case split on whether w_123 = x
                  by_cases hw_123_eq_x : w_123 = x
                  · -- w_123 = x, so we have w_123 = x and w_231 = y
                    -- Check w_213 to find a duplicate
                    have h_w213_exists : ∃ w, Survives setup [s2, s1, s3] w := survives_exists setup [s2, s1, s3] (by decide)
                    obtain ⟨w_213, hw_213⟩ := h_w213_exists

                    -- w_213 ∈ computeTopHalf s3 U_21
                    have hw_213_top : w_213 ∈ computeTopHalf setup s3 U_21 := by
                      unfold Survives at hw_213
                      simp only [List.foldl_cons, List.foldl_nil] at hw_213
                      exact hw_213

                    -- w_213 ∈ U_21 ⊆ I
                    have hw_213_I : w_213 ∈ I := by
                      have : computeTopHalf setup s3 U_21 ⊆ U_21 := by
                        unfold computeTopHalf
                        intro z hz
                        rw [Finset.mem_toFinset] at hz
                        have : z ∈ U_21.toList.mergeSort (fun a b => setup.score s3 a > setup.score s3 b) := by
                          exact List.mem_of_mem_take hz
                        rw [List.mem_mergeSort] at this
                        rw [← Finset.mem_toList]
                        exact this
                      have hw_213_U21 : w_213 ∈ U_21 := this hw_213_top
                      exact h_U21_subset_I hw_213_U21

                    -- Case split on whether x ∈ U_21
                    by_cases hx_U21 : x ∈ U_21
                    · -- x ∈ U_21, so w_213 = x (since x is best s3-scorer in I)
                      have hw_213_eq_x : w_213 = x := by
                        have hx_best_U21 : ∀ z ∈ U_21, setup.score s3 z ≤ setup.score s3 x := by
                          intro z hz
                          have hz_I : z ∈ I := h_U21_subset_I hz
                          exact hx_best z hz_I
                        have h_top_card : (computeTopHalf setup s3 U_21).card = 1 := by
                          rw [computeTopHalf_card, h_U21_card]
                          norm_num
                        have hx_in_top : x ∈ computeTopHalf setup s3 U_21 := by
                          apply max_score_in_computeTopHalf setup s3 U_21 x 1
                          · exact hx_U21
                          · exact hx_best_U21
                          · omega
                          · rw [h_U21_card]; omega
                        have h_singleton : ∃ a, computeTopHalf setup s3 U_21 = {a} := Finset.card_eq_one.mp h_top_card
                        obtain ⟨a, ha⟩ := h_singleton
                        rw [ha] at hx_in_top hw_213_top
                        rw [Finset.mem_singleton] at hx_in_top hw_213_top
                        rw [← hx_in_top, hw_213_top]

                      -- w_123 = x and w_213 = x, duplicate!
                      have h_dup : ∃ winner, Survives setup [s1, s2, s3] winner ∧ Survives setup [s2, s1, s3] winner := by
                        use x
                        constructor
                        · rw [← hw_123_eq_x]; exact hw_123
                        · rw [← hw_213_eq_x]; exact hw_213

                      obtain ⟨winner, hw1, hw2⟩ := h_dup
                      have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                        apply duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s2, s1, s3]
                        · intro h_eq
                          injection h_eq with h1 h_rest
                          injection h_rest
                        · decide
                        · decide
                        · exact hw1
                        · exact hw2
                      omega

                    · -- x ∉ U_21, so U_21 = I \ {x}
                      have h_U21_eq : U_21 = I \ {x} := by
                        have h_sub : U_21 ⊆ I \ {x} := by
                          intro z hz
                          rw [Finset.mem_sdiff]
                          constructor
                          · exact h_U21_subset_I hz
                          · rw [Finset.mem_singleton]
                            intro h_eq
                            rw [h_eq] at hz
                            exact hx_U21 hz
                        have h_diff_card : (I \ {x}).card = 2 := by
                          have hx_in_I : x ∈ I := hx_I
                          have : (I \ {x}).card = I.card - 1 := by
                            rw [Finset.card_sdiff]
                            · simp [Finset.card_singleton]
                            · exact Finset.singleton_subset_iff.mpr hx_in_I
                          rw [this, h_I_card]
                          omega
                        exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_U21_card, h_diff_card])

                      -- y ∈ U_21 (since U_21 = I \ {x} and y ∈ I, y ≠ x)
                      have hy_U21 : y ∈ U_21 := by
                        rw [h_U21_eq]
                        rw [Finset.mem_sdiff]
                        constructor
                        · exact hy_I
                        · rw [Finset.mem_singleton]
                          exact hy_ne_x

                      -- Case split on whether w_213 = y
                      by_cases hw_213_eq_y : w_213 = y
                      · -- w_213 = y and w_231 = y, duplicate!
                        have h_dup : ∃ winner, Survives setup [s2, s3, s1] winner ∧ Survives setup [s2, s1, s3] winner := by
                          use y
                          constructor
                          · rw [← h_w231_eq_y]; exact hw_231
                          · rw [← hw_213_eq_y]; exact hw_213

                        obtain ⟨winner, hw1, hw2⟩ := h_dup
                        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                          apply duplicate_winner_implies_count_le_five setup [s2, s3, s1] [s2, s1, s3]
                          · intro h_eq
                            injection h_eq with h1 h_rest
                            injection h_rest
                          · decide
                          · decide
                          · exact hw1
                          · exact hw2
                        omega

                      · -- w_213 ≠ y and w_213 ∈ U_21 = I \ {x}, so w_213 is the third element z of I
                        -- But this leads to a contradiction!
                        -- y is the second-best s3-scorer in I (after x)
                        -- U_21 = I \ {x} = {y, z} where z is the third element
                        -- w_213 is the best s3-scorer in U_21
                        -- If w_213 = z, then z has better s3-score than y
                        -- But y is second-best in I, so y has better s3-score than z
                        -- Contradiction!

                        -- w_213 ∈ U_21 = I \ {x}
                        have hw_213_in_U21 : w_213 ∈ U_21 := by
                          have : computeTopHalf setup s3 U_21 ⊆ U_21 := by
                            unfold computeTopHalf
                            intro w hw
                            rw [Finset.mem_toFinset] at hw
                            have : w ∈ U_21.toList.mergeSort (fun a b => setup.score s3 a > setup.score s3 b) := by
                              exact List.mem_of_mem_take hw
                            rw [List.mem_mergeSort] at this
                            rw [← Finset.mem_toList]
                            exact this
                          exact this hw_213_top

                        -- w_213 ∈ I (since U_21 ⊆ I)
                        have hw_213_I : w_213 ∈ I := h_U21_subset_I hw_213_in_U21

                        -- w_213 ∈ I \ {x} (since U_21 = I \ {x})
                        have hw_213_not_x : w_213 ≠ x := by
                          intro h_eq
                          rw [h_eq] at hw_213_in_U21
                          rw [h_U21_eq] at hw_213_in_U21
                          have : x ∈ I \ {x} := hw_213_in_U21
                          have : x ∉ I \ {x} := by
                            rw [Finset.mem_sdiff]
                            push_neg
                            intro _
                            rw [Finset.mem_singleton]
                          exact this hw_213_in_U21

                        -- So w_213 ∈ I and w_213 ≠ x and w_213 ≠ y
                        -- Since I has 3 elements {x, y, z}, w_213 must be z

                        -- Now show that y has better s3-score than w_213
                        -- y ∈ U_23 and U_23 is top 2 s3-scorers in S2
                        -- w_213 ∈ I ⊆ S2
                        -- If w_213 ∉ U_23, then w_213 has worse s3-score than elements in U_23
                        -- In particular, w_213 has worse s3-score than y

                        have h_y_better_w213 : setup.score s3 y > setup.score s3 w_213 := by
                          -- Check if w_213 ∈ U_23
                          by_cases hw_213_U23 : w_213 ∈ U_23
                          · -- w_213 ∈ U_23 = {x, y}
                            have h_U23_eq : U_23 = {x, y} := h_U23_eq
                            rw [h_U23_eq] at hw_213_U23
                            rw [Finset.mem_insert, Finset.mem_singleton] at hw_213_U23
                            cases hw_213_U23 with
                            | inl h => exact absurd h hw_213_not_x
                            | inr h => exact absurd h hw_213_eq_y
                          · -- w_213 ∉ U_23, so w_213 has worse s3-score than y
                            -- U_23 is top 2 in S2, w_213 ∈ S2 \ U_23
                            have hw_213_S2 : w_213 ∈ S2 := by
                              have : I ⊆ S2 := Finset.inter_subset_right
                              exact this hw_213_I
                            have hw_213_diff : w_213 ∈ S2 \ U_23 := by
                              rw [Finset.mem_sdiff]
                              exact ⟨hw_213_S2, hw_213_U23⟩
                            -- y ∈ U_23 ⊆ S2
                            have hy_U23_mem : y ∈ U_23 := hy_U23
                            -- U_23 = computeTopHalf s3 S2
                            unfold U_23 at hy_U23_mem hw_213_diff
                            -- Elements in computeTopHalf have better scores than elements outside
                            have : setup.score s3 y ≥ setup.score s3 w_213 := by
                              exact computeTopHalf_score_property setup s3 S2 y hy_U23_mem w_213 hw_213_diff
                            by_contra h_not_gt
                            push_neg at h_not_gt
                            have : setup.score s3 y = setup.score s3 w_213 := by omega
                            have h_inj := setup.score_injective s3
                            have : y = w_213 := h_inj this
                            exact hw_213_eq_y this.symm

                        -- But w_213 is the best s3-scorer in U_21
                        -- So w_213 has better s3-score than y (since y ∈ U_21)
                        have h_w213_better_y : setup.score s3 w_213 ≥ setup.score s3 y := by
                          -- w_213 ∈ computeTopHalf s3 U_21
                          -- y ∈ U_21 \ computeTopHalf s3 U_21
                          have hy_U21_mem : y ∈ U_21 := hy_U21
                          by_cases hy_top : y ∈ computeTopHalf setup s3 U_21
                          · -- y ∈ computeTopHalf s3 U_21
                            -- But |computeTopHalf s3 U_21| = 1
                            have h_top_card : (computeTopHalf setup s3 U_21).card = 1 := by
                              rw [computeTopHalf_card, h_U21_card]
                              norm_num
                            -- So computeTopHalf s3 U_21 = {w_213} = {y}
                            have : computeTopHalf setup s3 U_21 = {w_213} := by
                              have h_singleton : ∃ a, computeTopHalf setup s3 U_21 = {a} := Finset.card_eq_one.mp h_top_card
                              obtain ⟨a, ha⟩ := h_singleton
                              rw [ha] at hw_213_top
                              rw [Finset.mem_singleton] at hw_213_top
                              rw [← hw_213_top]
                              exact ha
                            rw [this] at hy_top
                            rw [Finset.mem_singleton] at hy_top
                            exact absurd hy_top.symm hw_213_eq_y
                          · -- y ∉ computeTopHalf s3 U_21
                            have hy_diff : y ∈ U_21 \ computeTopHalf setup s3 U_21 := by
                              rw [Finset.mem_sdiff]
                              exact ⟨hy_U21_mem, hy_top⟩
                            exact computeTopHalf_score_property setup s3 U_21 w_213 hw_213_top y hy_diff

                        -- Contradiction: y > w_213 and w_213 ≥ y
                        omega

                  · -- w_123 ≠ x, so w_123 is another element of I
                    -- Since w_123 ∈ I and w_123 ≠ x and w_123 ≠ y, w_123 = z (the third element)
                    -- We have w_123 = z, w_231 = y
                    -- Need to check for duplicates with other orderings
                    -- Show w_123 has strictly better s3-score than y
                    have hy_diff_top : y ∈ U_12 \ computeTopHalf setup s3 U_12 := by
                      exact Finset.mem_sdiff.mpr ⟨hy_U12, h_y_best_U12⟩
                    have h_score_w123_ge_y : setup.score s3 w_123 ≥ setup.score s3 y :=
                      computeTopHalf_score_property setup s3 U_12 w_123 hw_123_top y hy_diff_top
                    have h_score_w123_gt_y : setup.score s3 w_123 > setup.score s3 y := by
                      by_contra h_not_gt
                      push_neg at h_not_gt
                      have h_eq : setup.score s3 w_123 = setup.score s3 y := by omega
                      have h_inj := setup.score_injective s3
                      have : w_123 = y := h_inj h_eq
                      exact hw_123_ne_y this

                    -- w_123 ∈ S2 \ U_23 (since U_23 = {x, y})
                    have hw_123_S2 : w_123 ∈ S2 := by
                      have : I ⊆ S2 := Finset.inter_subset_right
                      exact this hw_123_I
                    have hw_123_not_U23 : w_123 ∉ U_23 := by
                      rw [h_U23_eq]
                      intro h_mem
                      rw [Finset.mem_insert, Finset.mem_singleton] at h_mem
                      cases h_mem with
                      | inl h => exact hw_123_eq_x h
                      | inr h => exact hw_123_ne_y h
                    have hw_123_diff : w_123 ∈ S2 \ U_23 :=
                      Finset.mem_sdiff.mpr ⟨hw_123_S2, hw_123_not_U23⟩

                    -- But y ∈ U_23 implies score y ≥ score w_123, contradiction
                    have h_score_y_ge_w123 : setup.score s3 y ≥ setup.score s3 w_123 :=
                      computeTopHalf_score_property setup s3 S2 y hy_U23 w_123 hw_123_diff
                    omega

              · -- y ∉ U_12, so check U_21
                by_cases hy_U21 : y ∈ U_21
                · -- Similar analysis for U_21
                  -- Pick winner for [s2, s1, s3]
                  have h_w213_exists : ∃ w, Survives setup [s2, s1, s3] w := survives_exists setup [s2, s1, s3] (by decide)
                  obtain ⟨w_213, hw_213⟩ := h_w213_exists
                  have hw_213_top : w_213 ∈ computeTopHalf setup s3 U_21 := by
                    unfold Survives at hw_213
                    simp only [List.foldl_cons, List.foldl_nil] at hw_213
                    exact hw_213

                  -- Case split on whether y is selected from U_21
                  by_cases hy_top : y ∈ computeTopHalf setup s3 U_21
                  · -- Then w_213 = y, duplicate with w_231 = y
                    have h_top_card : (computeTopHalf setup s3 U_21).card = 1 := by
                      rw [computeTopHalf_card, h_U21_card]
                      norm_num
                    have h_singleton : ∃ a, computeTopHalf setup s3 U_21 = {a} :=
                      Finset.card_eq_one.mp h_top_card
                    obtain ⟨a, ha⟩ := h_singleton
                    have hy_eq_a : y = a := by
                      have : y ∈ {a} := by simpa [ha] using hy_top
                      exact Finset.mem_singleton.mp this
                    have hw_eq_a : w_213 = a := by
                      have : w_213 ∈ {a} := by simpa [ha] using hw_213_top
                      exact Finset.mem_singleton.mp this
                    have h_w213_eq_y : w_213 = y := by
                      rw [hy_eq_a, hw_eq_a]

                    have h_dup : ∃ winner, Survives setup [s2, s1, s3] winner ∧ Survives setup [s2, s3, s1] winner := by
                      use y
                      constructor
                      · rw [← h_w213_eq_y]; exact hw_213
                      · rw [← h_w231_eq_y]; exact hw_231

                    obtain ⟨winner, hw1, hw2⟩ := h_dup
                    have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                      apply duplicate_winner_implies_count_le_five setup [s2, s1, s3] [s2, s3, s1]
                      · intro h_eq
                        injection h_eq with h1 h_rest
                        injection h_rest
                      · decide
                      · decide
                      · exact hw1
                      · exact hw2
                    omega
                  · -- y not in top-half of U_21
                    have hy_diff_top : y ∈ U_21 \ computeTopHalf setup s3 U_21 :=
                      Finset.mem_sdiff.mpr ⟨hy_U21, hy_top⟩
                    have h_score_w213_ge_y : setup.score s3 w_213 ≥ setup.score s3 y :=
                      computeTopHalf_score_property setup s3 U_21 w_213 hw_213_top y hy_diff_top
                    have h_score_w213_gt_y : setup.score s3 w_213 > setup.score s3 y := by
                      by_contra h_not_gt
                      push_neg at h_not_gt
                      have h_eq : setup.score s3 w_213 = setup.score s3 y := by omega
                      have h_inj := setup.score_injective s3
                      have : w_213 = y := h_inj h_eq
                      exact hy_top (by simpa [this] using hw_213_top)

                    -- Build w_123 and show w_123 = x (since y ∉ U_12)
                    have h_w123_exists : ∃ w, Survives setup [s1, s2, s3] w := survives_exists setup [s1, s2, s3] (by decide)
                    obtain ⟨w_123, hw_123⟩ := h_w123_exists
                    have h_U12_eq : U_12 = I \ {y} := by
                      have h_sub : U_12 ⊆ I \ {y} := by
                        intro z hz
                        rw [Finset.mem_sdiff]
                        constructor
                        · exact h_U12_subset_I hz
                        · rw [Finset.mem_singleton]
                          intro h_eq
                          rw [h_eq] at hz
                          exact hy_U12 hz
                      have h_diff_card : (I \ {y}).card = 2 := by
                        have hy_in_I : y ∈ I := hy_I
                        have : (I \ {y}).card = I.card - 1 := by
                          rw [Finset.card_sdiff]
                          · simp [Finset.card_singleton]
                          · exact Finset.singleton_subset_iff.mpr hy_in_I
                        rw [this, h_I_card]
                        omega
                      exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_U12_card, h_diff_card])
                    have hx_U12 : x ∈ U_12 := by
                      rw [h_U12_eq, Finset.mem_sdiff]
                      constructor
                      · exact hx_I
                      · rw [Finset.mem_singleton]
                        exact hy_ne_x.symm
                    have hw_123_top : w_123 ∈ computeTopHalf setup s3 U_12 := by
                      unfold Survives at hw_123
                      simp only [List.foldl_cons, List.foldl_nil] at hw_123
                      exact hw_123
                    have hw_123_eq_x : w_123 = x := by
                      have hx_best_U12 : ∀ z ∈ U_12, setup.score s3 z ≤ setup.score s3 x := by
                        intro z hz
                        have hz_I : z ∈ I := h_U12_subset_I hz
                        exact hx_best z hz_I
                      have h_top_card : (computeTopHalf setup s3 U_12).card = 1 := by
                        rw [computeTopHalf_card, h_U12_card]
                        norm_num
                      have hx_in_top : x ∈ computeTopHalf setup s3 U_12 := by
                        apply max_score_in_computeTopHalf setup s3 U_12 x 1
                        · exact hx_U12
                        · exact hx_best_U12
                        · omega
                        · rw [h_U12_card]; omega
                      have h_singleton : ∃ a, computeTopHalf setup s3 U_12 = {a} :=
                        Finset.card_eq_one.mp h_top_card
                      obtain ⟨a, ha⟩ := h_singleton
                      rw [ha] at hx_in_top hw_123_top
                      rw [Finset.mem_singleton] at hx_in_top hw_123_top
                      rw [← hx_in_top, hw_123_top]

                    -- If w_213 = x, duplicate with w_123
                    by_cases h_w213_eq_x : w_213 = x
                    · have h_dup : ∃ winner, Survives setup [s2, s1, s3] winner ∧ Survives setup [s1, s2, s3] winner := by
                        use x
                        constructor
                        · rw [← h_w213_eq_x]; exact hw_213
                        · rw [← hw_123_eq_x]; exact hw_123
                      obtain ⟨winner, hw1, hw2⟩ := h_dup
                      have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                        apply duplicate_winner_implies_count_le_five setup [s2, s1, s3] [s1, s2, s3]
                        · intro h_eq
                          injection h_eq with h1 h_rest
                          injection h_rest
                        · decide
                        · decide
                        · exact hw1
                        · exact hw2
                      omega
                    · -- w_213 ≠ x, so w_213 ∉ U_23 = {x, y}, contradicting y ∈ U_23 and score order
                      have h_w213_ne_y : w_213 ≠ y := by
                        intro h_eq
                        rw [h_eq] at hw_213_top
                        exact hy_top hw_213_top
                      have hw_213_S2 : w_213 ∈ S2 := by
                        have : U_21 ⊆ S2 := by
                          unfold U_21
                          exact computeTopHalf_subset setup s1 S2
                        exact this (computeTopHalf_subset setup s3 U_21 hw_213_top)
                      have hw_213_not_U23 : w_213 ∉ U_23 := by
                        rw [h_U23_eq]
                        intro h_mem
                        rw [Finset.mem_insert, Finset.mem_singleton] at h_mem
                        cases h_mem with
                        | inl h => exact h_w213_eq_x h
                        | inr h => exact h_w213_ne_y h
                      have hw_213_diff : w_213 ∈ S2 \ U_23 :=
                        Finset.mem_sdiff.mpr ⟨hw_213_S2, hw_213_not_U23⟩
                      have h_score_y_ge_w213 : setup.score s3 y ≥ setup.score s3 w_213 :=
                        computeTopHalf_score_property setup s3 S2 y hy_U23 w_213 hw_213_diff
                      omega
                · -- y ∉ U_12 and y ∉ U_21
                  -- But U_12 ∪ U_21 ⊆ I and |I| = 3, |U_12| = 2, |U_21| = 2
                  -- So |U_12 ∪ U_21| ≥ 2
                  -- If y ∉ U_12 ∪ U_21, then U_12 ∪ U_21 ⊆ I \ {y}
                  -- But |I \ {y}| = 2, so U_12 ∪ U_21 = I \ {y}
                  -- This means U_12 = U_21 = I \ {y} (since both have size 2)
                  -- But we already handled the U_12 = U_21 case earlier

                  -- Prove U_12 ⊆ I \ {y}
                  have h_U12_sub : U_12 ⊆ I \ {y} := by
                    intro z hz
                    rw [Finset.mem_sdiff]
                    constructor
                    · exact h_U12_subset_I hz
                    · rw [Finset.mem_singleton]
                      intro h_eq
                      rw [h_eq] at hz
                      exact hy_U12 hz

                  -- Prove U_21 ⊆ I \ {y}
                  have h_U21_sub : U_21 ⊆ I \ {y} := by
                    intro z hz
                    rw [Finset.mem_sdiff]
                    constructor
                    · exact h_U21_subset_I hz
                    · rw [Finset.mem_singleton]
                      intro h_eq
                      rw [h_eq] at hz
                      exact hy_U21 hz

                  -- |I \ {y}| = 2
                  have h_diff_card : (I \ {y}).card = 2 := by
                    have hy_in_I : y ∈ I := hy_I
                    have : (I \ {y}).card = I.card - 1 := by
                      rw [Finset.card_sdiff]
                      · simp [Finset.card_singleton]
                      · exact Finset.singleton_subset_iff.mpr hy_in_I
                    rw [this, h_I_card]
                    omega

                  -- So U_12 = I \ {y} and U_21 = I \ {y}
                  have h_U12_eq_diff : U_12 = I \ {y} := Finset.eq_of_subset_of_card_le h_U12_sub (by rw [h_U12_card, h_diff_card])
                  have h_U21_eq_diff : U_21 = I \ {y} := Finset.eq_of_subset_of_card_le h_U21_sub (by rw [h_U21_card, h_diff_card])

                  -- Therefore U_12 = U_21
                  have h_U12_eq_U21_contra : U_12 = U_21 := by
                    rw [h_U12_eq_diff, h_U21_eq_diff]

                  -- But we assumed U_12 ≠ U_21, contradiction!
                  exact h_U12_eq_U21 h_U12_eq_U21_contra


        exact h_count_le_5
      · -- |S1 ∩ S2| ≥ 4
        have h12_eq_4 : (S1 ∩ S2).card = 4 := by
          have : (S1 ∩ S2).card ≤ min S1.card S2.card := inter_card_le_min S1 S2
          rw [h_S1_card, h_S2_card] at this
          simp at this
          omega
        -- |S1 ∩ S2| = 4意味着S1 = S2
        have h_S1_eq_S2 : S1 = S2 := eq_of_inter_card_eq_four S1 S2 h_S1_card h_S2_card h12_eq_4
        -- According to the solution Case 2, when S1 = S2,
        -- the set {w_{ABC}, w_{BAC}, w_{ACB}, w_{BCA}} has at most 3 distinct elements
        -- This is because U_{AC} = U_{BC} (both are top 2 in C from S1=S2)
        -- and the analysis shows at most 3 distinct winners from these 4 orderings
        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          have h_le_6 := champions_le_six setup
          by_contra h_not_le_5
          push_neg at h_not_le_5
          have h_eq_6 : countPotentialChampions setup = 6 := by omega

          -- When S1 = S2, we analyze the 4 orderings involving s1 and s2
          -- Key insight: U_{s1,s3} = U_{s2,s3} (both are top 2 s3-ranked in S1=S2)
          -- Let Y = U_{s1,s3} = U_{s2,s3}

          -- Define the intermediate sets for the 4 orderings
          let U_12 := computeTopHalf setup s2 S1  -- Top 2 in s2 from S1
          let U_21 := computeTopHalf setup s1 S2  -- Top 2 in s1 from S2 = S1
          let U_13 := computeTopHalf setup s3 S1  -- Top 2 in s3 from S1
          let U_23 := computeTopHalf setup s3 S2  -- Top 2 in s3 from S2 = S1

          -- Since S1 = S2, we have U_13 = U_23
          have h_U13_eq_U23 : U_13 = U_23 := by
            unfold U_13 U_23
            rw [h_S1_eq_S2]

          let Y := U_13

          -- The winners w_{s1,s3,s2} and w_{s2,s3,s1} are both selected from Y
          -- So they are in Y

          -- Now consider w_{s1,s2,s3} and w_{s2,s1,s3}
          -- If U_12 ∩ Y ≠ ∅, then w_{s1,s2,s3} is the best s3-ranked in U_12
          -- Since Y contains the absolute best 2 s3-ranked students in S1,
          -- any student in U_12 ∩ Y beats all students in U_12 \ Y in s3
          -- So w_{s1,s2,s3} ∈ Y

          -- Similarly for w_{s2,s1,s3}

          -- To have all 4 winners distinct and outside Y (to get 6 total),
          -- we would need U_12 ∩ Y = ∅ and U_21 ∩ Y = ∅
          -- This means U_12 = S1 \ Y and U_21 = S1 \ Y
          -- So U_12 = U_21

          -- But if U_12 = U_21, then w_{s1,s2,s3} = w_{s2,s1,s3}
          -- (both are the best s3-ranked student in the same set)

          -- This gives us a duplication, contradicting count = 6

          -- Strategy: Show that among [s1,s2,s3], [s2,s1,s3], [s1,s3,s2], [s2,s3,s1],
          -- at least two produce the same winner

          -- Key observation: |Y| = 2, |S1| = 4, |U_12| = 2, |U_21| = 2
          have h_Y_card : Y.card = 2 := by
            unfold Y U_13
            exact computeTopHalf_card setup s3 S1

          have h_U12_card : U_12.card = 2 := computeTopHalf_card setup s2 S1
          have h_U21_card : U_21.card = 2 := by
            rw [← h_S1_eq_S2]
            exact computeTopHalf_card setup s1 S2

          -- Case analysis on whether U_12 and U_21 intersect Y
          by_cases h_U12_inter : (U_12 ∩ Y).Nonempty
          · -- U_12 ∩ Y ≠ ∅
            -- Strategy: Use computeTopHalf_score_property to show winner is in Y

            -- Y = computeTopHalf s3 S1 contains the top 2 s3-ranked students in S1
            -- By computeTopHalf_score_property: ∀ y ∈ Y, ∀ x ∈ S1 \ Y, score s3 y ≥ score s3 x

            have h_Y_top_scores : ∀ y ∈ Y, ∀ x ∈ S1 \ Y, setup.score s3 y ≥ setup.score s3 x := by
              unfold Y U_13
              exact computeTopHalf_score_property setup s3 S1

            -- U_12 ⊆ S1
            have h_U12_subset : U_12 ⊆ S1 := computeTopHalf_subset setup s2 S1

            -- For any u ∈ U_12 ∩ Y and v ∈ U_12 \ Y:
            -- u ∈ Y and v ∈ S1 \ Y (since v ∈ U_12 ⊆ S1 and v ∉ Y)
            -- Therefore score s3 u ≥ score s3 v

            have h_inter_better : ∀ u ∈ U_12 ∩ Y, ∀ v ∈ U_12 \ Y, setup.score s3 u ≥ setup.score s3 v := by
              intro u hu v hv
              have hu_Y : u ∈ Y := Finset.mem_inter.mp hu |>.2
              have hv_U12 : v ∈ U_12 := Finset.mem_sdiff.mp hv |>.1
              have hv_not_Y : v ∉ Y := Finset.mem_sdiff.mp hv |>.2
              have hv_S1 : v ∈ S1 := h_U12_subset hv_U12
              have hv_S1_diff_Y : v ∈ S1 \ Y := Finset.mem_sdiff.mpr ⟨hv_S1, hv_not_Y⟩
              exact h_Y_top_scores u hu_Y v hv_S1_diff_Y

            -- computeTopHalf s3 U_12 selects 1 student (the top s3-ranked from U_12)
            -- Since U_12 ∩ Y ≠ ∅ and elements in U_12 ∩ Y have higher scores,
            -- this student must be from U_12 ∩ Y ⊆ Y

            -- Prove that computeTopHalf s3 U_12 ⊆ U_12 ∩ Y (and hence ⊆ Y)
            have h_winner_in_inter : computeTopHalf setup s3 U_12 ⊆ U_12 ∩ Y := by
              intro w hw
              -- w is in computeTopHalf s3 U_12
              -- We need to show w ∈ U_12 ∩ Y

              have hw_U12 : w ∈ U_12 := computeTopHalf_subset setup s3 U_12 hw

              -- Show w ∈ Y by contradiction
              by_contra hw_not_Y
              -- Then w ∈ U_12 \ Y
              have hw_diff : w ∈ U_12 \ Y := Finset.mem_sdiff.mpr ⟨hw_U12, hw_not_Y⟩

              -- Pick any u ∈ U_12 ∩ Y (exists since nonempty)
              obtain ⟨u, hu_inter⟩ := h_U12_inter

              -- By h_inter_better: score s3 u ≥ score s3 w
              have h_score_u_ge_w : setup.score s3 u ≥ setup.score s3 w :=
                h_inter_better u hu_inter w hw_diff

              -- u is in U_12
              have hu_U12 : u ∈ U_12 := Finset.mem_inter.mp hu_inter |>.1

              -- Now we derive a contradiction:
              -- If u ∈ computeTopHalf s3 U_12, then both u and w are in it
              -- But |computeTopHalf s3 U_12| = 1, so u = w
              -- But u ∈ Y and w ∉ Y, contradiction

              -- If u ∉ computeTopHalf s3 U_12, then u ∈ U_12 \ computeTopHalf s3 U_12
              -- By computeTopHalf_score_property: score w ≥ score u
              -- But we have score u ≥ score w
              -- So score u = score w

              by_cases hu_in_top : u ∈ computeTopHalf setup s3 U_12
              · -- Both u and w are in computeTopHalf s3 U_12
                -- But |computeTopHalf s3 U_12| = 1
                have h_card_1 : (computeTopHalf setup s3 U_12).card = 1 := by
                  rw [computeTopHalf_card, h_U12_card]
                  norm_num
                -- So u = w
                have h_singleton : ∃ x, computeTopHalf setup s3 U_12 = {x} :=
                  Finset.card_eq_one.mp h_card_1
                obtain ⟨x, hx⟩ := h_singleton
                have hu_eq : u = x := by
                  have : u ∈ {x} := hx ▸ hu_in_top
                  exact Finset.mem_singleton.mp this
                have hw_eq : w = x := by
                  have : w ∈ {x} := hx ▸ hw
                  exact Finset.mem_singleton.mp this
                rw [hu_eq, hw_eq] at hw_not_Y
                have hu_Y : u ∈ Y := Finset.mem_inter.mp hu_inter |>.2
                rw [hu_eq] at hu_Y
                exact hw_not_Y hu_Y
              · -- u ∉ computeTopHalf s3 U_12
                -- Then u ∈ U_12 \ computeTopHalf s3 U_12
                have hu_diff_top : u ∈ U_12 \ computeTopHalf setup s3 U_12 :=
                  Finset.mem_sdiff.mpr ⟨hu_U12, hu_in_top⟩
                -- By computeTopHalf_score_property: score w ≥ score u
                have h_score_w_ge_u : setup.score s3 w ≥ setup.score s3 u :=
                  computeTopHalf_score_property setup s3 U_12 w hw u hu_diff_top
                -- But score u ≥ score w, so score u = score w
                have h_eq : setup.score s3 u = setup.score s3 w := by omega
                -- When scores are equal, we show u = w
                -- Both u and w are in U_12, and computeTopHalf selects exactly 1 element
                -- If they have equal scores, computeTopHalf's deterministic selection means
                -- the selected element is unique among those with the max score
                -- Since w is selected and u has the same score, u must equal w
                have hu_w_eq : u = w := by
                  -- We have: w ∈ computeTopHalf s3 U_12, u ∈ U_12, score u = score w
                  -- And |computeTopHalf s3 U_12| = 1
                  -- If u ≠ w, then both u and w are in U_12 with equal scores
                  -- But computeTopHalf selected w and not u
                  -- This means w's score > u's score (by computeTopHalf_score_property)
                  -- But we have score u = score w, contradiction
                  -- Therefore u = w
                  have h_inj := setup.score_injective s3
                  exact h_inj h_eq
                -- Now u = w, so w ∈ Y (since u ∈ Y)
                rw [← hu_w_eq] at hw_not_Y
                have hu_Y : u ∈ Y := Finset.mem_inter.mp hu_inter |>.2
                exact hw_not_Y hu_Y

            have h_winner_in_Y : computeTopHalf setup s3 U_12 ⊆ Y := by
              exact Finset.Subset.trans h_winner_in_inter Finset.inter_subset_right

            -- Now we have: computeTopHalf s3 U_12 ⊆ Y
            -- This means the winner w_{s1,s2,s3} ∈ Y
            -- We also have w_{s1,s3,s2} ∈ Y and w_{s2,s3,s1} ∈ Y (by definition of Y)
            -- So we have 3 orderings producing winners in Y, which has |Y| = 2
            -- By pigeonhole, at least two winners are identical

            -- The 3 orderings are: [s1,s2,s3], [s1,s3,s2], [s2,s3,s1]
            -- All produce winners in Y

            -- For [s1,s3,s2]: winner is in computeTopHalf s2 (computeTopHalf s3 S1) = computeTopHalf s2 Y
            -- For [s2,s3,s1]: winner is in computeTopHalf s1 (computeTopHalf s3 S2) = computeTopHalf s1 Y (since S1 = S2)

            -- Actually, let me use a simpler argument:
            -- We know that if count = 6, all 6 orderings produce distinct winners
            -- But we've shown that at least 3 orderings produce winners in Y (size 2)
            -- So at most 2 distinct winners from these 3 orderings
            -- This means at least one duplication among the 6 orderings
            -- Therefore count ≤ 5

            -- To formalize this properly, I need to show that having 3 winners in a set of size 2
            -- implies at least two are the same, then find which two orderings produce the same winner

            -- For now, let me use the fact that this contradicts count = 6
            have h_contradiction : countPotentialChampions setup ≤ 5 := by
              -- Strategy: Use pigeonhole principle
              -- 3 orderings ([s1,s2,s3], [s1,s3,s2], [s2,s3,s1]) produce winners in Y
              -- |Y| = 2, so by pigeonhole at least 2 orderings produce the same winner

              -- Define the 3 orderings
              let ord1 := [s1, s2, s3]
              let ord2 := [s1, s3, s2]
              let ord3 := [s2, s3, s1]

              -- Get the winners for each ordering
              have h_winner1 : ∃ w ∈ Y, Survives setup ord1 w := by
                -- Winner of ord1 is in computeTopHalf s3 U_12 ⊆ Y
                have h_surv : ∃ w, Survives setup ord1 w := survives_exists setup ord1 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                · -- Show w ∈ Y
                  unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw
                  -- ord1 = [s1, s2, s3]
                  -- After s1: S1 = computeTopHalf s1 S0
                  -- After s2: U_12 = computeTopHalf s2 S1
                  -- After s3: w ∈ computeTopHalf s3 U_12
                  have : w ∈ computeTopHalf setup s3 U_12 := hw
                  exact h_winner_in_Y this
                · exact hw

              have h_winner2 : ∃ w ∈ Y, Survives setup ord2 w := by
                -- Winner of ord2 is in computeTopHalf s2 Y ⊆ Y
                have h_surv : ∃ w, Survives setup ord2 w := survives_exists setup ord2 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                · -- Show w ∈ Y
                  unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw
                  -- ord2 = [s1, s3, s2]
                  -- After s1: S1
                  -- After s3: Y = computeTopHalf s3 S1
                  -- After s2: w ∈ computeTopHalf s2 Y ⊆ Y
                  exact computeTopHalf_subset setup s2 Y hw
                · exact hw

              have h_winner3 : ∃ w ∈ Y, Survives setup ord3 w := by
                -- Winner of ord3 is in computeTopHalf s1 Y ⊆ Y
                have h_surv : ∃ w, Survives setup ord3 w := survives_exists setup ord3 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                · -- Show w ∈ Y
                  unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw
                  -- ord3 = [s2, s3, s1]
                  -- After s2: S2 = S1 (by h_S1_eq_S2)
                  -- After s3: Y = computeTopHalf s3 S1
                  -- After s1: w ∈ computeTopHalf s1 Y ⊆ Y
                  exact computeTopHalf_subset setup s1 Y hw
                · exact hw

              -- By pigeonhole: 3 winners in Y (size 2) → at least 2 are the same
              obtain ⟨w1, hw1_Y, hw1_surv⟩ := h_winner1
              obtain ⟨w2, hw2_Y, hw2_surv⟩ := h_winner2
              obtain ⟨w3, hw3_Y, hw3_surv⟩ := h_winner3

              -- At least two of w1, w2, w3 must be equal
              by_cases h12 : w1 = w2
              · -- w1 = w2, so ord1 and ord2 produce the same winner
                rw [← h12] at hw2_surv
                apply duplicate_winner_implies_count_le_five setup ord1 ord2
                · -- ord1 ≠ ord2
                  intro h_eq
                  simp only [ord1, ord2] at h_eq
                  injection h_eq with _ h_rest
                  injection h_rest
                · -- ord1 is a permutation
                  decide
                · -- ord2 is a permutation
                  decide
                · exact hw1_surv
                · exact hw2_surv
              · by_cases h13 : w1 = w3
                · -- w1 = w3, so ord1 and ord3 produce the same winner
                  rw [← h13] at hw3_surv
                  apply duplicate_winner_implies_count_le_five setup ord1 ord3
                  · -- ord1 ≠ ord3
                    intro h_eq
                    simp only [ord1, ord3] at h_eq
                    injection h_eq
                  · decide
                  · decide
                  · exact hw1_surv
                  · exact hw3_surv
                · -- w1 ≠ w2 and w1 ≠ w3, so w2 = w3 (pigeonhole)
                  have h23 : w2 = w3 := by
                    -- Y has only 2 elements, and w1, w2, w3 are all in Y
                    -- If w1 ≠ w2 and w1 ≠ w3, then w2 = w3
                    by_contra h_ne
                    -- If w2 ≠ w3, then {w1, w2, w3} has 3 distinct elements
                    have h_three : ({w1, w2, w3} : Finset Student).card ≥ 3 := by
                      have : ({w1, w2, w3} : Finset Student).card = 3 := by
                        rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
                        · norm_num
                        · simp [h13]
                        · simp [h12, h_ne]
                      omega
                    -- But {w1, w2, w3} ⊆ Y and Y.card = 2
                    have h_subset : ({w1, w2, w3} : Finset Student) ⊆ Y := by
                      intro x hx
                      simp at hx
                      cases hx with
                      | inl h => rw [h]; exact hw1_Y
                      | inr h => cases h with
                        | inl h => rw [h]; exact hw2_Y
                        | inr h => rw [h]; exact hw3_Y
                    have h_le : ({w1, w2, w3} : Finset Student).card ≤ Y.card :=
                      Finset.card_le_card h_subset
                    rw [h_Y_card] at h_le
                    omega
                  rw [← h23] at hw3_surv
                  apply duplicate_winner_implies_count_le_five setup ord2 ord3
                  · -- ord2 ≠ ord3
                    intro h_eq
                    simp only [ord2, ord3] at h_eq
                    injection h_eq
                  · decide
                  · decide
                  · exact hw2_surv
                  · exact hw3_surv

            omega  -- Contradicts h_eq_6
          · -- U_12 ∩ Y = ∅
            push_neg at h_U12_inter
            have h_U12_disjoint : Disjoint U_12 Y := by
              rw [Finset.disjoint_iff_inter_eq_empty]
              exact Finset.not_nonempty_iff_eq_empty.mp h_U12_inter

            -- Since U_12 ⊆ S1, |U_12| = 2, |Y| = 2, |S1| = 4, and U_12 ∩ Y = ∅
            -- We have U_12 = S1 \ Y

            have h_U12_subset : U_12 ⊆ S1 := computeTopHalf_subset setup s2 S1
            have h_Y_subset : Y ⊆ S1 := by
              unfold Y U_13
              exact computeTopHalf_subset setup s3 S1

            have h_U12_eq_diff : U_12 = S1 \ Y := by
              -- U_12 ⊆ S1 \ Y (since U_12 ⊆ S1 and Disjoint U_12 Y)
              have h_sub : U_12 ⊆ S1 \ Y := by
                intro x hx
                rw [Finset.mem_sdiff]
                constructor
                · exact h_U12_subset hx
                · intro hx_Y
                  have : x ∈ U_12 ∩ Y := Finset.mem_inter.mpr ⟨hx, hx_Y⟩
                  exact Finset.disjoint_iff_inter_eq_empty.mp h_U12_disjoint ▸
                    Finset.not_mem_empty x this
              -- |S1 \ Y| = |S1| - |Y| = 4 - 2 = 2 = |U_12|
              have h_diff_card : (S1 \ Y).card = S1.card - Y.card :=
                Finset.card_sdiff h_Y_subset
              rw [h_S1_card, h_Y_card] at h_diff_card
              -- So |S1 \ Y| = 2 = |U_12|, and U_12 ⊆ S1 \ Y, hence U_12 = S1 \ Y
              exact Finset.eq_of_subset_of_card_le h_sub (by omega)

            -- Similarly, if U_21 ∩ Y = ∅, then U_21 = S1 \ Y
            by_cases h_U21_inter : (U_21 ∩ Y).Nonempty
            · -- U_21 ∩ Y ≠ ∅, so w_{s2,s1,s3} ∈ Y
              -- Combined with w_{s1,s3,s2} ∈ Y and w_{s2,s3,s1} ∈ Y
              -- We have 3 winners in Y (size 2), so duplication

              -- First, prove that computeTopHalf s3 U_21 ⊆ Y
              have h_U21_subset : U_21 ⊆ S1 := by
                unfold U_21
                rw [h_S1_eq_S2]
                exact computeTopHalf_subset setup s1 S2

              have h_inter_better_21 : ∀ u ∈ U_21 ∩ Y, ∀ v ∈ U_21 \ Y,
                  setup.score s3 u ≥ setup.score s3 v := by
                intro u hu v hv
                have hu_Y : u ∈ Y := Finset.mem_inter.mp hu |>.2
                have hv_U21 : v ∈ U_21 := Finset.mem_sdiff.mp hv |>.1
                have hv_not_Y : v ∉ Y := Finset.mem_sdiff.mp hv |>.2
                have hv_S1 : v ∈ S1 := h_U21_subset hv_U21
                have hv_S1_diff_Y : v ∈ S1 \ Y := Finset.mem_sdiff.mpr ⟨hv_S1, hv_not_Y⟩
                exact h_Y_top_scores u hu_Y v hv_S1_diff_Y

              have h_winner_21_in_Y : computeTopHalf setup s3 U_21 ⊆ Y := by
                intro w hw
                have hw_U21 : w ∈ U_21 := computeTopHalf_subset setup s3 U_21 hw
                by_contra hw_not_Y
                have hw_diff : w ∈ U_21 \ Y := Finset.mem_sdiff.mpr ⟨hw_U21, hw_not_Y⟩
                obtain ⟨u, hu_inter⟩ := h_U21_inter
                have h_score_u_ge_w : setup.score s3 u ≥ setup.score s3 w :=
                  h_inter_better_21 u hu_inter w hw_diff
                have hu_U21 : u ∈ U_21 := Finset.mem_inter.mp hu_inter |>.1
                by_cases hu_in_top : u ∈ computeTopHalf setup s3 U_21
                · have h_card_1 : (computeTopHalf setup s3 U_21).card = 1 := by
                    rw [computeTopHalf_card, h_U21_card]
                    norm_num
                  have h_singleton : ∃ x, computeTopHalf setup s3 U_21 = {x} :=
                    Finset.card_eq_one.mp h_card_1
                  obtain ⟨x, hx⟩ := h_singleton
                  have hu_eq : u = x := by
                    have : u ∈ {x} := hx ▸ hu_in_top
                    exact Finset.mem_singleton.mp this
                  have hw_eq : w = x := by
                    have : w ∈ {x} := hx ▸ hw
                    exact Finset.mem_singleton.mp this
                  rw [hu_eq, hw_eq] at hw_not_Y
                  have hu_Y : u ∈ Y := Finset.mem_inter.mp hu_inter |>.2
                  rw [hu_eq] at hu_Y
                  exact hw_not_Y hu_Y
                · have hu_diff_top : u ∈ U_21 \ computeTopHalf setup s3 U_21 :=
                    Finset.mem_sdiff.mpr ⟨hu_U21, hu_in_top⟩
                  have h_score_w_ge_u : setup.score s3 w ≥ setup.score s3 u :=
                    computeTopHalf_score_property setup s3 U_21 w hw u hu_diff_top
                  have h_eq : setup.score s3 u = setup.score s3 w := by omega
                  -- When scores are equal, show u = w
                  have hu_w_eq : u = w := by
                    have h_inj := setup.score_injective s3
                    exact h_inj h_eq
                  rw [← hu_w_eq] at hw_not_Y
                  have hu_Y : u ∈ Y := Finset.mem_inter.mp hu_inter |>.2
                  exact hw_not_Y hu_Y

              -- Now apply pigeonhole: 3 orderings produce winners in Y
              have h_contradiction : countPotentialChampions setup ≤ 5 := by
                let ord1 := [s1, s3, s2]
                let ord2 := [s2, s3, s1]
                let ord3 := [s2, s1, s3]

                have h_winner1 : ∃ w ∈ Y, Survives setup ord1 w := by
                  have h_surv : ∃ w, Survives setup ord1 w := survives_exists setup ord1 (by decide)
                  obtain ⟨w, hw⟩ := h_surv
                  use w
                  constructor
                  · unfold Survives at hw
                    simp only [List.foldl_cons, List.foldl_nil] at hw
                    exact computeTopHalf_subset setup s2 Y hw
                  · exact hw

                have h_winner2 : ∃ w ∈ Y, Survives setup ord2 w := by
                  have h_surv : ∃ w, Survives setup ord2 w := survives_exists setup ord2 (by decide)
                  obtain ⟨w, hw⟩ := h_surv
                  use w
                  constructor
                  · unfold Survives at hw
                    simp only [List.foldl_cons, List.foldl_nil] at hw
                    exact computeTopHalf_subset setup s1 Y hw
                  · exact hw

                have h_winner3 : ∃ w ∈ Y, Survives setup ord3 w := by
                  have h_surv : ∃ w, Survives setup ord3 w := survives_exists setup ord3 (by decide)
                  obtain ⟨w, hw⟩ := h_surv
                  use w
                  constructor
                  · unfold Survives at hw
                    simp only [List.foldl_cons, List.foldl_nil] at hw
                    exact h_winner_21_in_Y hw
                  · exact hw

                obtain ⟨w1, hw1_Y, hw1_surv⟩ := h_winner1
                obtain ⟨w2, hw2_Y, hw2_surv⟩ := h_winner2
                obtain ⟨w3, hw3_Y, hw3_surv⟩ := h_winner3

                by_cases h12 : w1 = w2
                · rw [← h12] at hw2_surv
                  apply duplicate_winner_implies_count_le_five setup ord1 ord2
                  · intro h_eq
                    simp only [ord1, ord2] at h_eq
                    injection h_eq
                  · decide
                  · decide
                  · exact hw1_surv
                  · exact hw2_surv
                · by_cases h13 : w1 = w3
                  · rw [← h13] at hw3_surv
                    apply duplicate_winner_implies_count_le_five setup ord1 ord3
                    · intro h_eq
                      simp only [ord1, ord3] at h_eq
                      injection h_eq with _ h_rest
                      injection h_rest
                    · decide
                    · decide
                    · exact hw1_surv
                    · exact hw3_surv
                  · have h23 : w2 = w3 := by
                      by_contra h_ne
                      have h_three : ({w1, w2, w3} : Finset Student).card ≥ 3 := by
                        have : ({w1, w2, w3} : Finset Student).card = 3 := by
                          rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
                          · norm_num
                          · simp [h13]
                          · simp [h12, h_ne]
                        omega
                      have h_subset : ({w1, w2, w3} : Finset Student) ⊆ Y := by
                        intro x hx
                        simp at hx
                        cases hx with
                        | inl h => rw [h]; exact hw1_Y
                        | inr h => cases h with
                          | inl h => rw [h]; exact hw2_Y
                          | inr h => rw [h]; exact hw3_Y
                      have h_le : ({w1, w2, w3} : Finset Student).card ≤ Y.card :=
                        Finset.card_le_card h_subset
                      rw [h_Y_card] at h_le
                      omega
                    rw [← h23] at hw3_surv
                    apply duplicate_winner_implies_count_le_five setup ord2 ord3
                    · intro h_eq
                      simp only [ord2, ord3] at h_eq
                      injection h_eq
                    · decide
                    · decide
                    · exact hw2_surv
                    · exact hw3_surv

              omega  -- Contradicts h_eq_6
            · -- U_21 ∩ Y = ∅
              push_neg at h_U21_inter
              have h_U21_disjoint : Disjoint U_21 Y := by
                rw [Finset.disjoint_iff_inter_eq_empty]
                exact Finset.not_nonempty_iff_eq_empty.mp h_U21_inter

              have h_U21_subset : U_21 ⊆ S2 := computeTopHalf_subset setup s1 S2
              have h_U21_subset' : U_21 ⊆ S1 := by rw [← h_S1_eq_S2]; exact h_U21_subset

              have h_U21_eq_diff : U_21 = S1 \ Y := by
                have h_sub : U_21 ⊆ S1 \ Y := by
                  intro x hx
                  rw [Finset.mem_sdiff]
                  constructor
                  · exact h_U21_subset' hx
                  · intro hx_Y
                    have : x ∈ U_21 ∩ Y := Finset.mem_inter.mpr ⟨hx, hx_Y⟩
                    exact Finset.disjoint_iff_inter_eq_empty.mp h_U21_disjoint ▸
                      Finset.not_mem_empty x this
                have h_diff_card : (S1 \ Y).card = S1.card - Y.card :=
                  Finset.card_sdiff h_Y_subset
                rw [h_S1_card, h_Y_card] at h_diff_card
                exact Finset.eq_of_subset_of_card_le h_sub (by omega)

              -- Now U_12 = S1 \ Y = U_21
              have h_U12_eq_U21 : U_12 = U_21 := by
                rw [h_U12_eq_diff, h_U21_eq_diff]

              -- Therefore, the final sets after applying s3 are equal
              -- S3 = computeTopHalf s3 U_12 = computeTopHalf s3 U_21 = S3'
              -- Since both are singletons, they contain the same winner

              have h_S3_eq : computeTopHalf setup s3 U_12 = computeTopHalf setup s3 U_21 := by
                rw [h_U12_eq_U21]

              -- Both orderings produce the same final set, hence the same winner
              -- We need to show that there exists a winner that survives both orderings

              have h_exists_winner : ∃ (winner : Student),
                  Survives setup [s1, s2, s3] winner ∧ Survives setup [s2, s1, s3] winner := by
                -- The final set S3 = computeTopHalf s3 U_12 is nonempty
                -- (since |U_12| = 2, so |S3| = 2/2 = 1)
                have h_S3_nonempty : (computeTopHalf setup s3 U_12).Nonempty := by
                  -- |U_12| = 2, so |computeTopHalf s3 U_12| = 2/2 = 1 > 0
                  have h_card : (computeTopHalf setup s3 U_12).card = U_12.card / 2 :=
                    computeTopHalf_card setup s3 U_12
                  rw [h_U12_card] at h_card
                  have : (computeTopHalf setup s3 U_12).card = 1 := by omega
                  exact Finset.card_pos.mp (by omega : 0 < (computeTopHalf setup s3 U_12).card)

                obtain ⟨winner, h_winner_mem⟩ := h_S3_nonempty

                use winner
                constructor
                · -- Survives [s1, s2, s3]
                  unfold Survives
                  simp only []
                  exact h_winner_mem
                · -- Survives [s2, s1, s3]
                  unfold Survives
                  simp only []
                  rw [← h_S3_eq]
                  exact h_winner_mem

              obtain ⟨winner, hw1, hw2⟩ := h_exists_winner

              -- Now apply duplicate_winner_implies_count_le_five
              have h_count_le_5' : countPotentialChampions setup ≤ 5 := by
                apply duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s2, s1, s3]
                · -- [s1,s2,s3] ≠ [s2,s1,s3]
                  intro h_eq
                  injection h_eq with h1 h2
                  exact hs12 h1
                · -- [s1,s2,s3] ~ univ.toList
                  have : (univ : Finset Subject).toList ~ ({s1, s2, s3} : Finset Subject).toList := by
                    apply List.Perm.of_eq
                    congr 1
                    exact huniv
                  apply List.Perm.trans _ this
                  have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s1, s2, s3} := rfl
                  rw [← h_finset_eq]
                  -- Prove [s1,s2,s3] ~ {s1,s2,s3}.toList
                  have h_s2_notin : s2 ∉ ({s3} : Finset Subject) := by
                    simp
                    exact hs23.symm
                  have h_s1_notin : s1 ∉ (insert s2 {s3} : Finset Subject) := by
                    simp
                    constructor
                    · exact hs12.symm
                    · exact hs13.symm
                  calc [s1, s2, s3]
                      = s1 :: s2 :: [s3] := rfl
                    _ = s1 :: s2 :: {s3}.toList := by rw [Finset.toList_singleton]
                    _ ~ s1 :: (insert s2 {s3}).toList := by
                        apply List.Perm.cons
                        exact (Finset.toList_insert h_s2_notin).symm
                    _ ~ (insert s1 (insert s2 {s3})).toList := by
                        exact (Finset.toList_insert h_s1_notin).symm
                    _ = ({s1, s2, s3} : Finset Subject).toList := rfl
                · -- [s2,s1,s3] ~ univ.toList
                  have : (univ : Finset Subject).toList ~ ({s1, s2, s3} : Finset Subject).toList := by
                    apply List.Perm.of_eq
                    congr 1
                    exact huniv
                  apply List.Perm.trans _ this
                  have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s2, s1, s3} := by
                    ext x
                    simp
                    tauto
                  rw [← h_finset_eq]
                  have h_s1_notin : s1 ∉ ({s3} : Finset Subject) := by
                    simp
                    exact hs13.symm
                  have h_s2_notin : s2 ∉ (insert s1 {s3} : Finset Subject) := by
                    simp
                    constructor
                    · exact hs12
                    · exact hs23.symm
                  calc [s2, s1, s3]
                      = s2 :: s1 :: [s3] := rfl
                    _ = s2 :: s1 :: {s3}.toList := by rw [Finset.toList_singleton]
                    _ ~ s2 :: (insert s1 {s3}).toList := by
                        apply List.Perm.cons
                        exact (Finset.toList_insert h_s1_notin).symm
                    _ ~ (insert s2 (insert s1 {s3})).toList := by
                        exact (Finset.toList_insert h_s2_notin).symm
                    _ = {s2, s1, s3}.toList := rfl
                · exact winner
                · exact hw1
                · exact hw2

              omega  -- Contradicts h_eq_6
        exact h_count_le_5
  · intro h_rest
    cases h_rest with
    | inl h23 =>
      -- Case 2: |S2 ∩ S3| ≥ 2
      -- This is symmetric to Case 1 (|S1 ∩ S2| ≥ 2)
      -- The same analysis applies with roles of subjects permuted

      -- Further analyze: could be 2, 3, or 4
      by_cases h23_eq_2 : (S2 ∩ S3).card = 2
      · -- |S2 ∩ S3| = 2
        -- By symmetry with size_two_intersection_property,
        -- orderings [s2,s3,s1] and [s3,s2,s1] produce the same winner

        -- We can prove this using the same argument as size_two_intersection_property
        -- but with s2, s3, s1 instead of s1, s2, s3

        -- For now, assume we have such a lemma and use it
        have h_exists_winner : ∃ (winner : Student),
            Survives setup [s2, s3, s1] winner ∧ Survives setup [s3, s2, s1] winner := by
          -- Apply size_two_intersection_property with permuted arguments
          -- This gives us the result for [s2,s3,s1] and [s3,s2,s1]
          apply size_two_intersection_property setup s2 s3 s1 hs23 hs13.symm hs12.symm
          -- Need to prove (survivalSet setup s2 ∩ survivalSet setup s3).card = 2
          exact h23_eq_2

        obtain ⟨winner, hw1, hw2⟩ := h_exists_winner

        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          -- Use the completed duplicate_winner_implies_count_le_five lemma
          apply duplicate_winner_implies_count_le_five setup [s2, s3, s1] [s3, s2, s1]
          · -- Prove [s2,s3,s1] ≠ [s3,s2,s1]
            intro h_eq
            injection h_eq with h1 h2
            exact hs23 h1.symm
          · -- Prove [s2,s3,s1] ~ univ.toList
            have : (univ : Finset Subject).toList ~ ({s1, s2, s3} : Finset Subject).toList := by
              apply List.Perm.of_eq
              congr 1
              exact huniv
            apply List.Perm.trans _ this
            -- Prove [s2,s3,s1] ~ {s1,s2,s3}.toList
            have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s2, s3, s1} := by
              ext x
              simp
              tauto
            rw [← h_finset_eq]
            -- Now prove [s2,s3,s1] ~ {s2,s3,s1}.toList
            have h_s3_notin : s3 ∉ ({s1} : Finset Subject) := by
              simp
              exact hs13.symm
            have h_s2_notin : s2 ∉ (insert s3 {s1} : Finset Subject) := by
              simp
              constructor
              · exact hs23.symm
              · exact hs12.symm
            calc [s2, s3, s1]
                = s2 :: s3 :: [s1] := rfl
              _ = s2 :: s3 :: {s1}.toList := by rw [Finset.toList_singleton]
              _ ~ s2 :: (insert s3 {s1}).toList := by
                  apply List.Perm.cons
                  exact (Finset.toList_insert h_s3_notin).symm
              _ ~ (insert s2 (insert s3 {s1})).toList := by
                  exact (Finset.toList_insert h_s2_notin).symm
              _ = {s2, s3, s1}.toList := rfl
          · -- Prove [s3,s2,s1] ~ univ.toList
            have : (univ : Finset Subject).toList ~ ({s1, s2, s3} : Finset Subject).toList := by
              apply List.Perm.of_eq
              congr 1
              exact huniv
            apply List.Perm.trans _ this
            have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s3, s2, s1} := by
              ext x
              simp
              tauto
            rw [← h_finset_eq]
            have h_s2_notin : s2 ∉ ({s1} : Finset Subject) := by
              simp
              exact hs12.symm
            have h_s3_notin : s3 ∉ (insert s2 {s1} : Finset Subject) := by
              simp
              constructor
              · exact hs23
              · exact hs13.symm
            calc [s3, s2, s1]
                = s3 :: s2 :: [s1] := rfl
              _ = s3 :: s2 :: {s1}.toList := by rw [Finset.toList_singleton]
              _ ~ s3 :: (insert s2 {s1}).toList := by
                  apply List.Perm.cons
                  exact (Finset.toList_insert h_s2_notin).symm
              _ ~ (insert s3 (insert s2 {s1})).toList := by
                  exact (Finset.toList_insert h_s3_notin).symm
              _ = {s3, s2, s1}.toList := rfl
          · exact winner
          · exact hw1
          · exact hw2

        exact h_count_le_5

      · -- |S2 ∩ S3| ≥ 3
        -- Similar analysis as for |S1 ∩ S2| ≥ 3
        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          have h_le_6 := champions_le_six setup
          by_contra h_not_le_5
          push_neg at h_not_le_5
          have h_eq_6 : countPotentialChampions setup = 6 := by omega
          -- Symmetric to |S1 ∩ S2| = 3 case
          -- Apply the same reasoning with s2, s3, s1 instead of s1, s2, s3
          -- The 3 orderings to consider are: [s2,s3,s1], [s3,s2,s1], [s3,s1,s2]
          -- At least two of these produce the same winner

          -- For now, accept this by symmetry
          -- Subdivide into = 3 and ≥ 4 cases
          by_cases h23_eq_3 : (S2 ∩ S3).card = 3
          · -- |S2 ∩ S3| = 3
            -- Symmetric to |S1 ∩ S2| = 3 case
            -- The 3 orderings to consider are: [s2,s3,s1], [s3,s2,s1], [s3,s1,s2]

            -- Let I = S2 ∩ S3 with |I| = 3
            let I := S2 ∩ S3
            have h_I_card : I.card = 3 := h23_eq_3

            -- Define intermediate sets (permuted from s1,s2,s3 to s2,s3,s1)
            let U_23 := computeTopHalf setup s3 S2  -- Top 2 in s3 from S2
            let U_32 := computeTopHalf setup s2 S3  -- Top 2 in s2 from S3
            let U_31 := computeTopHalf setup s1 S3  -- Top 2 in s1 from S3

            -- Prove U_23 ⊆ I and U_32 ⊆ I (symmetric to U_12 ⊆ I and U_21 ⊆ I)
            have h_U23_subset_I : U_23 ⊆ I := by
              have h_score_comparison : ∀ y ∈ I, ∀ z ∈ S2 \ I, setup.score s3 y > setup.score s3 z := by
                intro y hy z hz
                have hy_S3 : y ∈ S3 := Finset.mem_inter.mp hy |>.2
                have hz_not_S3 : z ∉ S3 := by
                  intro hz_S3
                  have hz_S2 : z ∈ S2 := Finset.mem_sdiff.mp hz |>.1
                  have : z ∈ I := Finset.mem_inter.mpr ⟨hz_S2, hz_S3⟩
                  exact Finset.not_mem_sdiff_of_mem this hz
                unfold S3 at hy_S3 hz_not_S3
                have : setup.score s3 y ≥ setup.score s3 z := by
                  have hz_univ : z ∈ univ := Finset.mem_univ z
                  have hz_diff : z ∈ univ \ survivalSet setup s3 := by
                    rw [Finset.mem_sdiff]
                    exact ⟨hz_univ, hz_not_S3⟩
                  unfold survivalSet at hy_S3 hz_diff
                  exact computeTopHalf_score_property setup s3 univ y hy_S3 z hz_diff
                by_contra h_not_gt
                push_neg at h_not_gt
                have : setup.score s3 y = setup.score s3 z := by omega
                have h_inj := setup.score_injective s3
                have : y = z := h_inj this
                rw [this] at hy
                have hz_S2 : z ∈ S2 := Finset.mem_sdiff.mp hz |>.1
                have : z ∈ I := hy
                exact Finset.not_mem_sdiff_of_mem this hz
              have h_I_subset_S2 : I ⊆ S2 := Finset.inter_subset_left
              have h_2_le_I : 2 ≤ I.card := by rw [h_I_card]; omega
              unfold U_23
              have : computeTopHalf setup s3 S2 =
                     (S2.toList.mergeSort (fun a b => setup.score s3 a > setup.score s3 b)).take 2 |>.toFinset := rfl
              rw [this]
              exact top_k_subset_of_high_scores S2 I (setup.score s3) 2 h_I_subset_S2 h_2_le_I h_score_comparison

            have h_U32_subset_I : U_32 ⊆ I := by
              have h_score_comparison : ∀ y ∈ I, ∀ z ∈ S3 \ I, setup.score s2 y > setup.score s2 z := by
                intro y hy z hz
                have hy_S2 : y ∈ S2 := Finset.mem_inter.mp hy |>.1
                have hz_not_S2 : z ∉ S2 := by
                  intro hz_S2
                  have hz_S3 : z ∈ S3 := Finset.mem_sdiff.mp hz |>.1
                  have : z ∈ I := Finset.mem_inter.mpr ⟨hz_S2, hz_S3⟩
                  exact Finset.not_mem_sdiff_of_mem this hz
                unfold S2 at hy_S2 hz_not_S2
                have : setup.score s2 y ≥ setup.score s2 z := by
                  have hz_univ : z ∈ univ := Finset.mem_univ z
                  have hz_diff : z ∈ univ \ survivalSet setup s2 := by
                    rw [Finset.mem_sdiff]
                    exact ⟨hz_univ, hz_not_S2⟩
                  unfold survivalSet at hy_S2 hz_diff
                  exact computeTopHalf_score_property setup s2 univ y hy_S2 z hz_diff
                by_contra h_not_gt
                push_neg at h_not_gt
                have : setup.score s2 y = setup.score s2 z := by omega
                have h_inj := setup.score_injective s2
                have : y = z := h_inj this
                rw [this] at hy
                have hz_S3 : z ∈ S3 := Finset.mem_sdiff.mp hz |>.1
                have : z ∈ I := hy
                exact Finset.not_mem_sdiff_of_mem this hz
              have h_I_subset_S3 : I ⊆ S3 := Finset.inter_subset_right
              have h_2_le_I : 2 ≤ I.card := by rw [h_I_card]; omega
              unfold U_32
              have : computeTopHalf setup s2 S3 =
                     (S3.toList.mergeSort (fun a b => setup.score s2 a > setup.score s2 b)).take 2 |>.toFinset := rfl
              rw [this]
              exact top_k_subset_of_high_scores S3 I (setup.score s2) 2 h_I_subset_S3 h_2_le_I h_score_comparison

            -- Rest of the proof follows the same structure
            -- Continue following |S1 ∩ S2| = 3 structure

            -- |U_23| = |U_32| = 2
            have h_U23_card : U_23.card = 2 := by
              unfold U_23
              exact computeTopHalf_card setup s3 S2
            have h_U32_card : U_32.card = 2 := by
              unfold U_32
              exact computeTopHalf_card setup s2 S3

            -- If U_23 = U_32, then the first two orderings yield the same winner
            by_cases h_U23_eq_U32 : U_23 = U_32
            · have h_dup : ∃ winner, Survives setup [s2, s3, s1] winner ∧ Survives setup [s3, s2, s1] winner := by
                have h_surv1 : ∃ w, Survives setup [s2, s3, s1] w :=
                  survives_exists setup [s2, s3, s1] (by decide)
                obtain ⟨w, hw⟩ := h_surv1
                use w
                constructor
                · exact hw
                · unfold Survives at hw ⊢
                  simp only [List.foldl_cons, List.foldl_nil] at hw ⊢
                  rw [h_U23_eq_U32]
                  exact hw
              obtain ⟨winner, hw1, hw2⟩ := h_dup
              have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                apply duplicate_winner_implies_count_le_five setup [s2, s3, s1] [s3, s2, s1]
                · intro h_eq
                  injection h_eq with h1 h2
                  exact hs23 h1.symm
                · decide
                · decide
                · exact hw1
                · exact hw2
              omega

            · -- U_23 ≠ U_32
              have h_I_nonempty : I.Nonempty := by
                rw [Finset.card_pos]
                rw [h_I_card]
                omega

              -- choose x: best s1-scorer in I
              have h_exists_best : ∃ x ∈ I, ∀ z ∈ I, setup.score s1 z ≤ setup.score s1 x := by
                exact Finset.exists_max_image I (setup.score s1) h_I_nonempty
              obtain ⟨x, hx_I, hx_best⟩ := h_exists_best

              -- show x ∈ U_31
              have h_I_subset_S3 : I ⊆ S3 := Finset.inter_subset_right
              have hx_in_U31 : x ∈ U_31 := by
                have hx_in_S3 : x ∈ S3 := h_I_subset_S3 hx_I
                apply at_most_k_minus_1_better_implies_in_top_k setup s1 S3 x 2
                · exact hx_in_S3
                · omega
                · rw [h_S3_card]; omega
                · -- at most 1 student in S3 has better s1 score than x
                  have h_better_in_diff :
                      S3.filter (fun y => setup.score s1 y > setup.score s1 x) ⊆ S3 \ I := by
                    intro y hy
                    rw [Finset.mem_filter] at hy
                    rw [Finset.mem_sdiff]
                    constructor
                    · exact hy.1
                    · intro hy_I
                      have : setup.score s1 y ≤ setup.score s1 x := hx_best y hy_I
                      omega
                  have h_diff_card : (S3 \ I).card ≤ 1 := by
                    have : (S3 \ I).card = S3.card - I.card := by
                      rw [Finset.card_sdiff h_I_subset_S3]
                    rw [this, h_S3_card, h_I_card]
                    omega
                  have := Finset.card_le_card h_better_in_diff
                  omega

              -- Analyze ordering [s3, s1, s2]
              have h_w312_exists : ∃ w, Survives setup [s3, s1, s2] w :=
                survives_exists setup [s3, s1, s2] (by decide)
              obtain ⟨w_312, hw_312⟩ := h_w312_exists

              by_cases h_w312_eq_x : w_312 = x
              · -- if w_312 = x, then x must be in U_23 or U_32, yielding a duplicate
                by_cases hx_U23 : x ∈ U_23
                · -- w_231 = x, duplicate with w_312
                  have h_w231_exists : ∃ w, Survives setup [s2, s3, s1] w :=
                    survives_exists setup [s2, s3, s1] (by decide)
                  obtain ⟨w_231, hw_231⟩ := h_w231_exists
                  have hw_231_eq_x : w_231 = x := by
                    have hx_best_U23 : ∀ z ∈ U_23, setup.score s1 z ≤ setup.score s1 x := by
                      intro z hz
                      have hz_I : z ∈ I := h_U23_subset_I hz
                      exact hx_best z hz_I
                    have h_top_card : (computeTopHalf setup s1 U_23).card = 1 := by
                      rw [computeTopHalf_card, h_U23_card]
                      norm_num
                    have hx_in_top : x ∈ computeTopHalf setup s1 U_23 := by
                      apply max_score_in_computeTopHalf setup s1 U_23 x 1
                      · exact hx_U23
                      · exact hx_best_U23
                      · omega
                      · rw [h_U23_card]; omega
                    have h_singleton : ∃ a, computeTopHalf setup s1 U_23 = {a} :=
                      Finset.card_eq_one.mp h_top_card
                    obtain ⟨a, ha⟩ := h_singleton
                    unfold Survives at hw_231
                    simp only [List.foldl_cons, List.foldl_nil] at hw_231
                    rw [ha] at hx_in_top hw_231
                    rw [Finset.mem_singleton] at hx_in_top hw_231
                    rw [← hx_in_top, hw_231]
                  have h_dup : ∃ winner, Survives setup [s2, s3, s1] winner ∧ Survives setup [s3, s1, s2] winner := by
                    use x
                    constructor
                    · rw [← hw_231_eq_x]; exact hw_231
                    · rw [← h_w312_eq_x]; exact hw_312
                  obtain ⟨winner, hw1, hw2⟩ := h_dup
                  have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                    apply duplicate_winner_implies_count_le_five setup [s2, s3, s1] [s3, s1, s2]
                    · intro h_eq
                      injection h_eq with h1 h2
                      exact hs23 h1.symm
                    · decide
                    · decide
                    · exact hw1
                    · exact hw2
                  omega
                · -- x ∉ U_23, so x ∈ U_32 (otherwise U_23 = U_32)
                  by_cases hx_U32 : x ∈ U_32
                  · -- w_321 = x, duplicate with w_312
                    have h_w321_exists : ∃ w, Survives setup [s3, s2, s1] w :=
                      survives_exists setup [s3, s2, s1] (by decide)
                    obtain ⟨w_321, hw_321⟩ := h_w321_exists
                    have hw_321_eq_x : w_321 = x := by
                      have hx_best_U32 : ∀ z ∈ U_32, setup.score s1 z ≤ setup.score s1 x := by
                        intro z hz
                        have hz_I : z ∈ I := h_U32_subset_I hz
                        exact hx_best z hz_I
                      have h_top_card : (computeTopHalf setup s1 U_32).card = 1 := by
                        rw [computeTopHalf_card, h_U32_card]
                        norm_num
                      have hx_in_top : x ∈ computeTopHalf setup s1 U_32 := by
                        apply max_score_in_computeTopHalf setup s1 U_32 x 1
                        · exact hx_U32
                        · exact hx_best_U32
                        · omega
                        · rw [h_U32_card]; omega
                      have h_singleton : ∃ a, computeTopHalf setup s1 U_32 = {a} :=
                        Finset.card_eq_one.mp h_top_card
                      obtain ⟨a, ha⟩ := h_singleton
                      unfold Survives at hw_321
                      simp only [List.foldl_cons, List.foldl_nil] at hw_321
                      rw [ha] at hx_in_top hw_321
                      rw [Finset.mem_singleton] at hx_in_top hw_321
                      rw [← hx_in_top, hw_321]
                    have h_dup : ∃ winner, Survives setup [s3, s2, s1] winner ∧ Survives setup [s3, s1, s2] winner := by
                      use x
                      constructor
                      · rw [← hw_321_eq_x]; exact hw_321
                      · rw [← h_w312_eq_x]; exact hw_312
                    obtain ⟨winner, hw1, hw2⟩ := h_dup
                    have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                      apply duplicate_winner_implies_count_le_five setup [s3, s2, s1] [s3, s1, s2]
                      · intro h_eq
                        injection h_eq with h1 h2
                        exact hs12 h2
                      · decide
                      · decide
                      · exact hw1
                      · exact hw2
                    omega
                  · -- x ∉ U_23 and x ∉ U_32 implies U_23 = U_32 = I \ {x}
                    have h_U23_sub : U_23 ⊆ I \ {x} := by
                      intro z hz
                      rw [Finset.mem_sdiff]
                      constructor
                      · exact h_U23_subset_I hz
                      · rw [Finset.mem_singleton]
                        intro h_eq
                        rw [h_eq] at hz
                        exact hx_U23 hz
                    have h_U32_sub : U_32 ⊆ I \ {x} := by
                      intro z hz
                      rw [Finset.mem_sdiff]
                      constructor
                      · exact h_U32_subset_I hz
                      · rw [Finset.mem_singleton]
                        intro h_eq
                        rw [h_eq] at hz
                        exact hx_U32 hz
                    have h_diff_card : (I \ {x}).card = 2 := by
                      have : (I \ {x}).card = I.card - 1 := by
                        rw [Finset.card_sdiff]
                        · simp [Finset.card_singleton]
                        · exact Finset.singleton_subset_iff.mpr hx_I
                      rw [this, h_I_card]
                      omega
                    have h_U23_eq : U_23 = I \ {x} :=
                      Finset.eq_of_subset_of_card_le h_U23_sub (by rw [h_U23_card, h_diff_card])
                    have h_U32_eq : U_32 = I \ {x} :=
                      Finset.eq_of_subset_of_card_le h_U32_sub (by rw [h_U32_card, h_diff_card])
                    exact h_U23_eq_U32 (by rw [h_U23_eq, h_U32_eq])

              · -- w_312 ≠ x
                -- Similar to original case: derive contradiction with score comparisons
                -- Since w_312 is chosen from U_31 and x is best s1 in I,
                -- we can reuse the structure to get a duplicate or contradiction.
                -- For simplicity, use the same contradiction approach as above by
                -- forcing a duplicate via U_23 or U_32.
                -- (This mirrors the original proof flow.)
                have h_w231_exists : ∃ w, Survives setup [s2, s3, s1] w :=
                  survives_exists setup [s2, s3, s1] (by decide)
                obtain ⟨w_231, hw_231⟩ := h_w231_exists
                have h_w321_exists : ∃ w, Survives setup [s3, s2, s1] w :=
                  survives_exists setup [s3, s2, s1] (by decide)
                obtain ⟨w_321, hw_321⟩ := h_w321_exists
                -- If w_231 = w_321, we are done
                by_cases h_eq : w_231 = w_321
                · have h_dup : ∃ winner, Survives setup [s2, s3, s1] winner ∧ Survives setup [s3, s2, s1] winner := by
                    use w_231
                    constructor
                    · exact hw_231
                    · rw [h_eq] at hw_321; exact hw_321
                  obtain ⟨winner, hw1, hw2⟩ := h_dup
                  have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                    apply duplicate_winner_implies_count_le_five setup [s2, s3, s1] [s3, s2, s1]
                    · intro h_eq'
                      injection h_eq' with h1 h2
                      exact hs23 h1.symm
                    · decide
                    · decide
                    · exact hw1
                    · exact hw2
                  omega
                · -- Otherwise, use pigeonhole with [s2,s3,s1], [s3,s2,s1], [s3,s1,s2]
                  -- to force a duplicate among three winners in size-2 subsets
                  have h_three : ({w_231, w_321, w_312} : Finset Student).card ≥ 3 := by
                    by_contra h_not
                    push_neg at h_not
                    -- If not ≥ 3, then at least two are equal
                    have h_dup : w_231 = w_321 ∨ w_231 = w_312 ∨ w_321 = w_312 := by
                      -- simple finite set card argument
                      have : ({w_231, w_321, w_312} : Finset Student).card ≤ 2 := by omega
                      -- use pigeonhole: if 3 distinct then card=3
                      by_contra h_all
                      push_neg at h_all
                      have : ({w_231, w_321, w_312} : Finset Student).card = 3 := by
                        have h_nodup : w_231 ≠ w_321 ∧ w_231 ≠ w_312 ∧ w_321 ≠ w_312 := h_all
                        have h1 : w_321 ≠ w_231 := h_nodup.1.symm
                        have h2 : w_312 ≠ w_231 := h_nodup.2.1.symm
                        have h3 : w_312 ≠ w_321 := h_nodup.2.2.symm
                        rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
                        · simp
                        · simp [h3]
                        · simp [h2]
                      omega
                    cases h_dup with
                    | inl h =>
                      have h_dup' : ∃ winner, Survives setup [s2, s3, s1] winner ∧ Survives setup [s3, s2, s1] winner := by
                        use w_231
                        constructor
                        · exact hw_231
                        · rw [h] at hw_321; exact hw_321
                      obtain ⟨winner, hw1, hw2⟩ := h_dup'
                      have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                        apply duplicate_winner_implies_count_le_five setup [s2, s3, s1] [s3, s2, s1]
                        · intro h_eq'
                          injection h_eq' with h1 h2
                          exact hs23 h1.symm
                        · decide
                        · decide
                        · exact hw1
                        · exact hw2
                      omega
                    | inr h =>
                      cases h with
                      | inl h =>
                        have h_dup' : ∃ winner, Survives setup [s2, s3, s1] winner ∧ Survives setup [s3, s1, s2] winner := by
                          use w_231
                          constructor
                          · exact hw_231
                          · rw [h] at hw_312; exact hw_312
                        obtain ⟨winner, hw1, hw2⟩ := h_dup'
                        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                          apply duplicate_winner_implies_count_le_five setup [s2, s3, s1] [s3, s1, s2]
                          · intro h_eq'
                            injection h_eq' with h1 h2
                            exact hs23 h1.symm
                          · decide
                          · decide
                          · exact hw1
                          · exact hw2
                        omega
                      | inr h =>
                        have h_dup' : ∃ winner, Survives setup [s3, s2, s1] winner ∧ Survives setup [s3, s1, s2] winner := by
                          use w_321
                          constructor
                          · exact hw_321
                          · rw [h] at hw_312; exact hw_312
                        obtain ⟨winner, hw1, hw2⟩ := h_dup'
                        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                          apply duplicate_winner_implies_count_le_five setup [s3, s2, s1] [s3, s1, s2]
                          · intro h_eq'
                            injection h_eq' with h1 h2
                            exact hs12 h2
                          · decide
                          · decide
                          · exact hw1
                          · exact hw2
                        omega

          · -- |S2 ∩ S3| ≥ 4
            have h23_eq_4 : (S2 ∩ S3).card = 4 := by
              have : (S2 ∩ S3).card ≤ min S2.card S3.card := inter_card_le_min S2 S3
              rw [h_S2_card, h_S3_card] at this
              simp at this
              omega
            -- S2 = S3
            have h_S2_eq_S3 : S2 = S3 := eq_of_inter_card_eq_four S2 S3 h_S2_card h_S3_card h23_eq_4
            -- Similar analysis as for S1 = S2 case
            have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
              have h_le_6 := champions_le_six setup
              by_contra h_not_le_5
              push_neg at h_not_le_5
              have h_eq_6 : countPotentialChampions setup = 6 := by omega

              -- Define intermediate sets
              let U_23 := computeTopHalf setup s3 S2
              let U_32 := computeTopHalf setup s2 S3
              let U_21 := computeTopHalf setup s1 S2
              let U_31 := computeTopHalf setup s1 S3

              have h_U21_eq_U31 : U_21 = U_31 := by
                unfold U_21 U_31
                rw [h_S2_eq_S3]

              let Y := U_21
              have h_Y_card : Y.card = 2 := by
                unfold Y U_21
                exact computeTopHalf_card setup s1 S2
              have h_U23_card : U_23.card = 2 := by
                unfold U_23
                exact computeTopHalf_card setup s3 S2
              have h_U32_card : U_32.card = 2 := by
                unfold U_32
                exact computeTopHalf_card setup s2 S3

              -- Winners for [s2,s1,s3] and [s3,s1,s2] are in Y
              let ord1 := [s2, s1, s3]
              let ord2 := [s3, s1, s2]
              let ord3 := [s2, s3, s1]
              let ord4 := [s3, s2, s1]

              have h_winner1 : ∃ w ∈ Y, Survives setup ord1 w := by
                have h_surv : ∃ w, Survives setup ord1 w := survives_exists setup ord1 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                · unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw
                  -- w ∈ computeTopHalf s3 Y ⊆ Y
                  exact computeTopHalf_subset setup s3 Y hw
                · exact hw

              have h_winner2 : ∃ w ∈ Y, Survives setup ord2 w := by
                have h_surv : ∃ w, Survives setup ord2 w := survives_exists setup ord2 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                · unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw
                  -- w ∈ computeTopHalf s2 Y ⊆ Y
                  exact computeTopHalf_subset setup s2 Y hw
                · exact hw

              -- If U_23 ∩ Y is nonempty, winner of ord3 is in Y
              by_cases h_U23_inter : (U_23 ∩ Y).Nonempty
              · have h_winner3 : ∃ w ∈ Y, Survives setup ord3 w := by
                  have h_surv : ∃ w, Survives setup ord3 w := survives_exists setup ord3 (by decide)
                  obtain ⟨w, hw⟩ := h_surv
                  use w
                  constructor
                  · unfold Survives at hw
                    simp only [List.foldl_cons, List.foldl_nil] at hw
                    -- show winner in Y via score comparison
                    -- elements in U_23 ∩ Y beat U_23 \ Y in s1
                    have h_score : ∀ u ∈ U_23 ∩ Y, ∀ v ∈ U_23 \ Y,
                        setup.score s1 u ≥ setup.score s1 v := by
                      intro u hu v hv
                      have hu_Y : u ∈ Y := Finset.mem_inter.mp hu |>.2
                      have hv_U23 : v ∈ U_23 := Finset.mem_sdiff.mp hv |>.1
                      have hv_not_Y : v ∉ Y := Finset.mem_sdiff.mp hv |>.2
                      have hv_S2 : v ∈ S2 := by
                        have : U_23 ⊆ S2 := by
                          unfold U_23
                          exact computeTopHalf_subset setup s3 S2
                        exact this hv_U23
                      have hv_S2_diff_Y : v ∈ S2 \ Y := Finset.mem_sdiff.mpr ⟨hv_S2, hv_not_Y⟩
                      have hu_S2 : u ∈ S2 := by
                        have : U_23 ⊆ S2 := by
                          unfold U_23
                          exact computeTopHalf_subset setup s3 S2
                        exact this (Finset.mem_inter.mp hu |>.1)
                      have hu_Y' : u ∈ Y := hu_Y
                      -- Y = computeTopHalf s1 S2, so elements of Y score ≥ elements outside
                      unfold Y U_21 at hu_Y' hv_S2_diff_Y
                      exact computeTopHalf_score_property setup s1 S2 u hu_Y' v hv_S2_diff_Y
                    have h_winner_in_Y : computeTopHalf setup s1 U_23 ⊆ Y := by
                      intro w hw'
                      have hw_U23 : w ∈ U_23 := computeTopHalf_subset setup s1 U_23 hw'
                      by_contra hw_not_Y
                      have hw_diff : w ∈ U_23 \ Y := Finset.mem_sdiff.mpr ⟨hw_U23, hw_not_Y⟩
                      obtain ⟨u, hu_inter⟩ := h_U23_inter
                      have h_score_u_ge_w : setup.score s1 u ≥ setup.score s1 w :=
                        h_score u hu_inter w hw_diff
                      -- w is chosen from top half of U_23, so w has score ≥ u
                      have h_score_w_ge_u : setup.score s1 w ≥ setup.score s1 u := by
                        have hu_U23 : u ∈ U_23 := Finset.mem_inter.mp hu_inter |>.1
                        by_cases hu_top : u ∈ computeTopHalf setup s1 U_23
                        · have h_card_1 : (computeTopHalf setup s1 U_23).card = 1 := by
                            rw [computeTopHalf_card, h_U23_card]
                            norm_num
                          have h_singleton : ∃ x, computeTopHalf setup s1 U_23 = {x} :=
                            Finset.card_eq_one.mp h_card_1
                          obtain ⟨x, hx⟩ := h_singleton
                          have hu_eq : u = x := by
                            have : u ∈ {x} := by simpa [hx] using hu_top
                            exact Finset.mem_singleton.mp this
                          have hw_eq : w = x := by
                            have : w ∈ {x} := by simpa [hx] using hw'
                            exact Finset.mem_singleton.mp this
                          rw [hu_eq, hw_eq]
                        · have hu_diff : u ∈ U_23 \ computeTopHalf setup s1 U_23 :=
                            Finset.mem_sdiff.mpr ⟨hu_U23, hu_top⟩
                          exact computeTopHalf_score_property setup s1 U_23 w hw' u hu_diff
                      have h_eq : setup.score s1 u = setup.score s1 w := by omega
                      have h_inj := setup.score_injective s1
                      have : u = w := h_inj h_eq
                      exact hw_not_Y (by simpa [this] using (Finset.mem_inter.mp hu_inter |>.2))
                    exact h_winner_in_Y hw
                  · exact hw

                obtain ⟨w1, hw1_Y, hw1_surv⟩ := h_winner1
                obtain ⟨w2, hw2_Y, hw2_surv⟩ := h_winner2
                obtain ⟨w3, hw3_Y, hw3_surv⟩ := h_winner3
                by_cases h12 : w1 = w2
                · apply duplicate_winner_implies_count_le_five setup ord1 ord2
                  · intro h_eq
                    simp only [ord1, ord2] at h_eq
                    injection h_eq
                  · decide
                  · decide
                  · exact hw1_surv
                  · rw [← h12] at hw2_surv; exact hw2_surv
                · by_cases h13 : w1 = w3
                  · apply duplicate_winner_implies_count_le_five setup ord1 ord3
                    · intro h_eq
                      simp only [ord1, ord3] at h_eq
                      injection h_eq with h1 hrest
                      injection hrest
                    · decide
                    · decide
                    · exact hw1_surv
                    · rw [← h13] at hw3_surv; exact hw3_surv
                  · have h23 : w2 = w3 := by
                      by_contra h_ne
                      have h_three : ({w1, w2, w3} : Finset Student).card = 3 := by
                        have h1 : w2 ≠ w1 := by exact h12.symm
                        have h2 : w3 ≠ w1 := by exact h13.symm
                        have h3 : w3 ≠ w2 := by exact h_ne
                        rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
                        · simp
                        · simp [h3]
                        · simp [h2]
                      -- But all three in Y of size 2
                      have h_Y_card' : (Y : Finset Student).card = 2 := h_Y_card
                      have : ({w1, w2, w3} : Finset Student).card ≤ Y.card := by
                        apply Finset.card_le_card
                        intro z hz
                        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
                        cases hz with
                        | inl h => rw [h]; exact hw1_Y
                        | inr h =>
                          cases h with
                          | inl h => rw [h]; exact hw2_Y
                          | inr h => rw [h]; exact hw3_Y
                      rw [h_three, h_Y_card] at this
                      omega
                    apply duplicate_winner_implies_count_le_five setup ord2 ord3
                    · intro h_eq
                      simp only [ord2, ord3] at h_eq
                      injection h_eq with h1 hrest
                      injection hrest
                    · decide
                    · decide
                    · exact hw2_surv
                    · rw [← h23] at hw3_surv; exact hw3_surv

              · -- U_23 ∩ Y = ∅, so U_23 = S2 \ Y
                have h_U23_sub : U_23 ⊆ S2 \ Y := by
                  intro z hz
                  rw [Finset.mem_sdiff]
                  constructor
                  · have : U_23 ⊆ S2 := by
                      unfold U_23
                      exact computeTopHalf_subset setup s3 S2
                    exact this hz
                  · intro hzY
                    have : z ∈ U_23 ∩ Y := by
                      exact ⟨hz, hzY⟩
                    exact (Finset.not_mem_empty _ (by
                      have h_empty : (U_23 ∩ Y) = ∅ := by
                        rw [Finset.not_nonempty_iff_eq_empty] at h_U23_inter
                        exact h_U23_inter
                      simpa [h_empty] using this))
                have h_diff_card : (S2 \ Y).card = 2 := by
                  have h_sub : Y ⊆ S2 := by
                    unfold Y U_21
                    exact computeTopHalf_subset setup s1 S2
                  have : (S2 \ Y).card = S2.card - Y.card := by
                    rw [Finset.card_sdiff h_sub]
                  rw [this, h_S2_card, h_Y_card]
                  omega
                have h_U23_eq : U_23 = S2 \ Y :=
                  Finset.eq_of_subset_of_card_le h_U23_sub (by rw [h_U23_card, h_diff_card])

                -- similarly for U_32
                have h_U32_sub : U_32 ⊆ S3 \ Y := by
                  intro z hz
                  rw [Finset.mem_sdiff]
                  constructor
                  · have : U_32 ⊆ S3 := by
                      unfold U_32
                      exact computeTopHalf_subset setup s2 S3
                    exact this hz
                  · intro hzY
                    have : z ∈ U_32 ∩ Y := by
                      exact ⟨hz, hzY⟩
                    have h_empty : (U_32 ∩ Y) = ∅ := by
                      -- if U_23 ∩ Y = ∅ then also U_32 ∩ Y = ∅ by symmetry
                      -- assume same reasoning; use by_contra to avoid extra lemma
                      by_contra h_ne
                      have h_nonempty : (U_32 ∩ Y).Nonempty := by
                        rw [Finset.nonempty_iff_ne_empty]
                        exact h_ne
                      -- If U_32 ∩ Y is nonempty, the previous case would give count ≤ 5
                      exact (h_U23_inter (by
                        -- derive a contradiction by using S2=S3 and U_23=U_32
                        -- use the fact that S2=S3 to transport nonempty
                        have : U_23 = U_32 := by
                          unfold U_23 U_32
                          rw [h_S2_eq_S3]
                        simpa [this] using h_nonempty))
                    simpa [h_empty] using this
                have h_diff_card' : (S3 \ Y).card = 2 := by
                  have h_sub : Y ⊆ S3 := by
                    unfold Y U_21
                    rw [h_S2_eq_S3]
                    exact computeTopHalf_subset setup s1 S2
                  have : (S3 \ Y).card = S3.card - Y.card := by
                    rw [Finset.card_sdiff h_sub]
                  rw [this, h_S3_card, h_Y_card]
                  omega
                have h_U32_eq : U_32 = S3 \ Y :=
                  Finset.eq_of_subset_of_card_le h_U32_sub (by rw [h_U32_card, h_diff_card'])

                -- Therefore U_23 = U_32 (since S2 = S3)
                have h_U23_eq_U32 : U_23 = U_32 := by
                  rw [h_U23_eq, h_U32_eq, h_S2_eq_S3]

                -- Duplicate between ord3 and ord4
                have h_dup : ∃ winner, Survives setup ord3 winner ∧ Survives setup ord4 winner := by
                  have h_surv : ∃ w, Survives setup ord3 w := survives_exists setup ord3 (by decide)
                  obtain ⟨w, hw⟩ := h_surv
                  use w
                  constructor
                  · exact hw
                  · unfold Survives at hw ⊢
                    simp only [List.foldl_cons, List.foldl_nil] at hw ⊢
                    rw [h_U23_eq_U32]
                    exact hw
                obtain ⟨winner, hw1, hw2⟩ := h_dup
                have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                  apply duplicate_winner_implies_count_le_five setup ord3 ord4
                  · intro h_eq
                    simp only [ord3, ord4] at h_eq
                    injection h_eq with h1 h2
                    exact hs23 h1.symm
                  · decide
                  · decide
                  · exact hw1
                  · exact hw2
                omega

            exact h_count_le_5

        exact h_count_le_5
    | inr h31 =>
      -- Case 3: |S3 ∩ S1| ≥ 2
      -- This is also symmetric to Case 1 (|S1 ∩ S2| ≥ 2)
      -- The same analysis applies with roles of subjects permuted

      -- Further analyze: could be 2, 3, or 4
      by_cases h31_eq_2 : (S3 ∩ S1).card = 2
      · -- |S3 ∩ S1| = 2
        -- By symmetry with size_two_intersection_property,
        -- orderings [s3,s1,s2] and [s1,s3,s2] produce the same winner

        have h_exists_winner : ∃ (winner : Student),
            Survives setup [s3, s1, s2] winner ∧ Survives setup [s1, s3, s2] winner := by
          -- Apply size_two_intersection_property with permuted arguments
          -- This gives us the result for [s3,s1,s2] and [s1,s3,s2]
          apply size_two_intersection_property setup s3 s1 s2 hs13 hs12 hs23
          -- Need to prove (survivalSet setup s3 ∩ survivalSet setup s1).card = 2
          exact h31_eq_2

        obtain ⟨winner, hw1, hw2⟩ := h_exists_winner

        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          -- Use the completed duplicate_winner_implies_count_le_five lemma
          apply duplicate_winner_implies_count_le_five setup [s3, s1, s2] [s1, s3, s2]
          · -- Prove [s3,s1,s2] ≠ [s1,s3,s2]
            intro h_eq
            injection h_eq with h1 h2
            exact hs13 h1
          · -- Prove [s3,s1,s2] ~ univ.toList
            have : (univ : Finset Subject).toList ~ ({s1, s2, s3} : Finset Subject).toList := by
              apply List.Perm.of_eq
              congr 1
              exact huniv
            apply List.Perm.trans _ this
            -- Prove [s3,s1,s2] ~ {s1,s2,s3}.toList
            have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s3, s1, s2} := by
              ext x
              simp
              tauto
            rw [← h_finset_eq]
            -- Now prove [s3,s1,s2] ~ {s3,s1,s2}.toList
            have h_s1_notin : s1 ∉ ({s2} : Finset Subject) := by
              simp
              exact hs12.symm
            have h_s3_notin : s3 ∉ (insert s1 {s2} : Finset Subject) := by
              simp
              constructor
              · exact hs13.symm
              · exact hs23.symm
            calc [s3, s1, s2]
                = s3 :: s1 :: [s2] := rfl
              _ = s3 :: s1 :: {s2}.toList := by rw [Finset.toList_singleton]
              _ ~ s3 :: (insert s1 {s2}).toList := by
                  apply List.Perm.cons
                  exact (Finset.toList_insert h_s1_notin).symm
              _ ~ (insert s3 (insert s1 {s2})).toList := by
                  exact (Finset.toList_insert h_s3_notin).symm
              _ = {s3, s1, s2}.toList := rfl
          · -- Prove [s1,s3,s2] ~ univ.toList
            have : (univ : Finset Subject).toList ~ ({s1, s2, s3} : Finset Subject).toList := by
              apply List.Perm.of_eq
              congr 1
              exact huniv
            apply List.Perm.trans _ this
            have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s1, s3, s2} := by
              ext x
              simp
              tauto
            rw [← h_finset_eq]
            have h_s3_notin : s3 ∉ ({s2} : Finset Subject) := by
              simp
              exact hs23.symm
            have h_s1_notin : s1 ∉ (insert s3 {s2} : Finset Subject) := by
              simp
              constructor
              · exact hs13.symm
              · exact hs12.symm
            calc [s1, s3, s2]
                = s1 :: s3 :: [s2] := rfl
              _ = s1 :: s3 :: {s2}.toList := by rw [Finset.toList_singleton]
              _ ~ s1 :: (insert s3 {s2}).toList := by
                  apply List.Perm.cons
                  exact (Finset.toList_insert h_s3_notin).symm
              _ ~ (insert s1 (insert s3 {s2})).toList := by
                  exact (Finset.toList_insert h_s1_notin).symm
              _ = {s1, s3, s2}.toList := rfl
          · exact winner
          · exact hw1
          · exact hw2

        exact h_count_le_5

      · -- |S3 ∩ S1| ≥ 3
        -- Similar analysis as for |S1 ∩ S2| ≥ 3
        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          have h_le_6 := champions_le_six setup
          by_contra h_not_le_5
          push_neg at h_not_le_5
          have h_eq_6 : countPotentialChampions setup = 6 := by omega
          -- Symmetric to |S1 ∩ S2| = 3 case
          -- Apply the same reasoning with s3, s1, s2 instead of s1, s2, s3
          -- The 3 orderings to consider are: [s3,s1,s2], [s1,s3,s2], [s1,s2,s3]
          -- At least two of these produce the same winner

          -- For now, accept this by symmetry
          -- Subdivide into = 3 and ≥ 4 cases
          by_cases h31_eq_3 : (S3 ∩ S1).card = 3
          · -- |S3 ∩ S1| = 3
            -- Symmetric to |S1 ∩ S2| = 3 case
            -- The 3 orderings to consider are: [s3,s1,s2], [s1,s3,s2], [s1,s2,s3]

            -- Let I = S3 ∩ S1 with |I| = 3
            let I := S3 ∩ S1
            have h_I_card : I.card = 3 := h31_eq_3

            -- Define intermediate sets (permuted from s1,s2,s3 to s3,s1,s2)
            let U_31 := computeTopHalf setup s1 S3  -- Top 2 in s1 from S3
            let U_13 := computeTopHalf setup s3 S1  -- Top 2 in s3 from S1
            let U_12 := computeTopHalf setup s2 S1  -- Top 2 in s2 from S1

            -- Prove U_31 ⊆ I and U_13 ⊆ I (symmetric to U_12 ⊆ I and U_21 ⊆ I)
            have h_U31_subset_I : U_31 ⊆ I := by
              have h_score_comparison : ∀ y ∈ I, ∀ z ∈ S3 \ I, setup.score s1 y > setup.score s1 z := by
                intro y hy z hz
                have hy_S1 : y ∈ S1 := Finset.mem_inter.mp hy |>.2
                have hz_not_S1 : z ∉ S1 := by
                  intro hz_S1
                  have hz_S3 : z ∈ S3 := Finset.mem_sdiff.mp hz |>.1
                  have : z ∈ I := Finset.mem_inter.mpr ⟨hz_S3, hz_S1⟩
                  exact Finset.not_mem_sdiff_of_mem this hz
                unfold S1 at hy_S1 hz_not_S1
                have : setup.score s1 y ≥ setup.score s1 z := by
                  have hz_univ : z ∈ univ := Finset.mem_univ z
                  have hz_diff : z ∈ univ \ survivalSet setup s1 := by
                    rw [Finset.mem_sdiff]
                    exact ⟨hz_univ, hz_not_S1⟩
                  unfold survivalSet at hy_S1 hz_diff
                  exact computeTopHalf_score_property setup s1 univ y hy_S1 z hz_diff
                by_contra h_not_gt
                push_neg at h_not_gt
                have : setup.score s1 y = setup.score s1 z := by omega
                have h_inj := setup.score_injective s1
                have : y = z := h_inj this
                rw [this] at hy
                have hz_S3 : z ∈ S3 := Finset.mem_sdiff.mp hz |>.1
                have : z ∈ I := hy
                exact Finset.not_mem_sdiff_of_mem this hz
              have h_I_subset_S3 : I ⊆ S3 := Finset.inter_subset_left
              have h_2_le_I : 2 ≤ I.card := by rw [h_I_card]; omega
              unfold U_31
              have : computeTopHalf setup s1 S3 =
                     (S3.toList.mergeSort (fun a b => setup.score s1 a > setup.score s1 b)).take 2 |>.toFinset := rfl
              rw [this]
              exact top_k_subset_of_high_scores S3 I (setup.score s1) 2 h_I_subset_S3 h_2_le_I h_score_comparison

            have h_U13_subset_I : U_13 ⊆ I := by
              have h_score_comparison : ∀ y ∈ I, ∀ z ∈ S1 \ I, setup.score s3 y > setup.score s3 z := by
                intro y hy z hz
                have hy_S3 : y ∈ S3 := Finset.mem_inter.mp hy |>.1
                have hz_not_S3 : z ∉ S3 := by
                  intro hz_S3
                  have hz_S1 : z ∈ S1 := Finset.mem_sdiff.mp hz |>.1
                  have : z ∈ I := Finset.mem_inter.mpr ⟨hz_S3, hz_S1⟩
                  exact Finset.not_mem_sdiff_of_mem this hz
                unfold S3 at hy_S3 hz_not_S3
                have : setup.score s3 y ≥ setup.score s3 z := by
                  have hz_univ : z ∈ univ := Finset.mem_univ z
                  have hz_diff : z ∈ univ \ survivalSet setup s3 := by
                    rw [Finset.mem_sdiff]
                    exact ⟨hz_univ, hz_not_S3⟩
                  unfold survivalSet at hy_S3 hz_diff
                  exact computeTopHalf_score_property setup s3 univ y hy_S3 z hz_diff
                by_contra h_not_gt
                push_neg at h_not_gt
                have : setup.score s3 y = setup.score s3 z := by omega
                have h_inj := setup.score_injective s3
                have : y = z := h_inj this
                rw [this] at hy
                have hz_S1 : z ∈ S1 := Finset.mem_sdiff.mp hz |>.1
                have : z ∈ I := hy
                exact Finset.not_mem_sdiff_of_mem this hz
              have h_I_subset_S1 : I ⊆ S1 := Finset.inter_subset_right
              have h_2_le_I : 2 ≤ I.card := by rw [h_I_card]; omega
              unfold U_13
              have : computeTopHalf setup s3 S1 =
                     (S1.toList.mergeSort (fun a b => setup.score s3 a > setup.score s3 b)).take 2 |>.toFinset := rfl
              rw [this]
              exact top_k_subset_of_high_scores S1 I (setup.score s3) 2 h_I_subset_S1 h_2_le_I h_score_comparison

            -- Rest of the proof follows the same structure
            -- Continue following |S1 ∩ S2| = 3 structure
            have h_U31_card : U_31.card = 2 := by
              unfold U_31
              exact computeTopHalf_card setup s1 S3
            have h_U13_card : U_13.card = 2 := by
              unfold U_13
              exact computeTopHalf_card setup s3 S1

            -- If U_31 = U_13, then [s3,s1,s2] and [s1,s3,s2] share winner
            by_cases h_U31_eq_U13 : U_31 = U_13
            · have h_dup : ∃ winner, Survives setup [s3, s1, s2] winner ∧ Survives setup [s1, s3, s2] winner := by
                have h_surv1 : ∃ w, Survives setup [s3, s1, s2] w :=
                  survives_exists setup [s3, s1, s2] (by decide)
                obtain ⟨w, hw⟩ := h_surv1
                use w
                constructor
                · exact hw
                · unfold Survives at hw ⊢
                  simp only [List.foldl_cons, List.foldl_nil] at hw ⊢
                  rw [h_U31_eq_U13]
                  exact hw
              obtain ⟨winner, hw1, hw2⟩ := h_dup
              have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                apply duplicate_winner_implies_count_le_five setup [s3, s1, s2] [s1, s3, s2]
                · intro h_eq
                  injection h_eq with h1 h2
                  exact hs13 h1
                · decide
                · decide
                · exact hw1
                · exact hw2
              omega

            · -- U_31 ≠ U_13
              have h_I_nonempty : I.Nonempty := by
                rw [Finset.card_pos]
                rw [h_I_card]
                omega
              -- choose x: best s2-scorer in I
              have h_exists_best : ∃ x ∈ I, ∀ z ∈ I, setup.score s2 z ≤ setup.score s2 x := by
                exact Finset.exists_max_image I (setup.score s2) h_I_nonempty
              obtain ⟨x, hx_I, hx_best⟩ := h_exists_best

              -- show x ∈ U_12
              have h_I_subset_S1 : I ⊆ S1 := Finset.inter_subset_right
              have hx_in_U12 : x ∈ U_12 := by
                have hx_in_S1 : x ∈ S1 := h_I_subset_S1 hx_I
                apply at_most_k_minus_1_better_implies_in_top_k setup s2 S1 x 2
                · exact hx_in_S1
                · omega
                · rw [h_S1_card]; omega
                · -- at most 1 student in S1 has better s2 score than x
                  have h_better_in_diff :
                      S1.filter (fun y => setup.score s2 y > setup.score s2 x) ⊆ S1 \ I := by
                    intro y hy
                    rw [Finset.mem_filter] at hy
                    rw [Finset.mem_sdiff]
                    constructor
                    · exact hy.1
                    · intro hy_I
                      have : setup.score s2 y ≤ setup.score s2 x := hx_best y hy_I
                      omega
                  have h_diff_card : (S1 \ I).card ≤ 1 := by
                    have : (S1 \ I).card = S1.card - I.card := by
                      rw [Finset.card_sdiff h_I_subset_S1]
                    rw [this, h_S1_card, h_I_card]
                    omega
                  have := Finset.card_le_card h_better_in_diff
                  omega

              -- Analyze ordering [s1, s2, s3]
              have h_w123_exists : ∃ w, Survives setup [s1, s2, s3] w :=
                survives_exists setup [s1, s2, s3] (by decide)
              obtain ⟨w_123, hw_123⟩ := h_w123_exists

              by_cases h_w123_eq_x : w_123 = x
              · -- if w_123 = x, then x in U_31 or U_13 gives duplicate
                by_cases hx_U31 : x ∈ U_31
                · have h_w312_exists : ∃ w, Survives setup [s3, s1, s2] w :=
                    survives_exists setup [s3, s1, s2] (by decide)
                  obtain ⟨w_312, hw_312⟩ := h_w312_exists
                  have hw_312_eq_x : w_312 = x := by
                    have hx_best_U31 : ∀ z ∈ U_31, setup.score s2 z ≤ setup.score s2 x := by
                      intro z hz
                      have hz_I : z ∈ I := h_U31_subset_I hz
                      exact hx_best z hz_I
                    have h_top_card : (computeTopHalf setup s2 U_31).card = 1 := by
                      rw [computeTopHalf_card, h_U31_card]
                      norm_num
                    have hx_in_top : x ∈ computeTopHalf setup s2 U_31 := by
                      apply max_score_in_computeTopHalf setup s2 U_31 x 1
                      · exact hx_U31
                      · exact hx_best_U31
                      · omega
                      · rw [h_U31_card]; omega
                    have h_singleton : ∃ a, computeTopHalf setup s2 U_31 = {a} :=
                      Finset.card_eq_one.mp h_top_card
                    obtain ⟨a, ha⟩ := h_singleton
                    unfold Survives at hw_312
                    simp only [List.foldl_cons, List.foldl_nil] at hw_312
                    rw [ha] at hx_in_top hw_312
                    rw [Finset.mem_singleton] at hx_in_top hw_312
                    rw [← hx_in_top, hw_312]
                  have h_dup : ∃ winner, Survives setup [s1, s2, s3] winner ∧ Survives setup [s3, s1, s2] winner := by
                    use x
                    constructor
                    · rw [← h_w123_eq_x]; exact hw_123
                    · rw [← hw_312_eq_x]; exact hw_312
                  obtain ⟨winner, hw1, hw2⟩ := h_dup
                  have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                    apply duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s3, s1, s2]
                    · intro h_eq
                      injection h_eq with h1 h2
                      exact hs13 h1.symm
                    · decide
                    · decide
                    · exact hw1
                    · exact hw2
                  omega
                · by_cases hx_U13 : x ∈ U_13
                  · have h_w132_exists : ∃ w, Survives setup [s1, s3, s2] w :=
                      survives_exists setup [s1, s3, s2] (by decide)
                    obtain ⟨w_132, hw_132⟩ := h_w132_exists
                    have hw_132_eq_x : w_132 = x := by
                      have hx_best_U13 : ∀ z ∈ U_13, setup.score s2 z ≤ setup.score s2 x := by
                        intro z hz
                        have hz_I : z ∈ I := h_U13_subset_I hz
                        exact hx_best z hz_I
                      have h_top_card : (computeTopHalf setup s2 U_13).card = 1 := by
                        rw [computeTopHalf_card, h_U13_card]
                        norm_num
                      have hx_in_top : x ∈ computeTopHalf setup s2 U_13 := by
                        apply max_score_in_computeTopHalf setup s2 U_13 x 1
                        · exact hx_U13
                        · exact hx_best_U13
                        · omega
                        · rw [h_U13_card]; omega
                      have h_singleton : ∃ a, computeTopHalf setup s2 U_13 = {a} :=
                        Finset.card_eq_one.mp h_top_card
                      obtain ⟨a, ha⟩ := h_singleton
                      unfold Survives at hw_132
                      simp only [List.foldl_cons, List.foldl_nil] at hw_132
                      rw [ha] at hx_in_top hw_132
                      rw [Finset.mem_singleton] at hx_in_top hw_132
                      rw [← hx_in_top, hw_132]
                    have h_dup : ∃ winner, Survives setup [s1, s2, s3] winner ∧ Survives setup [s1, s3, s2] winner := by
                      use x
                      constructor
                      · rw [← h_w123_eq_x]; exact hw_123
                      · rw [← hw_132_eq_x]; exact hw_132
                    obtain ⟨winner, hw1, hw2⟩ := h_dup
                    have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                      apply duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s1, s3, s2]
                      · intro h_eq
                        injection h_eq with h1 h2
                        exact hs23 h2
                      · decide
                      · decide
                      · exact hw1
                      · exact hw2
                    omega
                  · -- x ∉ U_31 and x ∉ U_13 implies U_31 = U_13 = I \ {x}
                    have h_U31_sub : U_31 ⊆ I \ {x} := by
                      intro z hz
                      rw [Finset.mem_sdiff]
                      constructor
                      · exact h_U31_subset_I hz
                      · rw [Finset.mem_singleton]
                        intro h_eq
                        rw [h_eq] at hz
                        exact hx_U31 hz
                    have h_U13_sub : U_13 ⊆ I \ {x} := by
                      intro z hz
                      rw [Finset.mem_sdiff]
                      constructor
                      · exact h_U13_subset_I hz
                      · rw [Finset.mem_singleton]
                        intro h_eq
                        rw [h_eq] at hz
                        exact hx_U13 hz
                    have h_diff_card : (I \ {x}).card = 2 := by
                      have : (I \ {x}).card = I.card - 1 := by
                        rw [Finset.card_sdiff]
                        · simp [Finset.card_singleton]
                        · exact Finset.singleton_subset_iff.mpr hx_I
                      rw [this, h_I_card]
                      omega
                    have h_U31_eq : U_31 = I \ {x} :=
                      Finset.eq_of_subset_of_card_le h_U31_sub (by rw [h_U31_card, h_diff_card])
                    have h_U13_eq : U_13 = I \ {x} :=
                      Finset.eq_of_subset_of_card_le h_U13_sub (by rw [h_U13_card, h_diff_card])
                    exact h_U31_eq_U13 (by rw [h_U31_eq, h_U13_eq])

              · -- w_123 ≠ x: force duplicate among orderings
                have h_w312_exists : ∃ w, Survives setup [s3, s1, s2] w :=
                  survives_exists setup [s3, s1, s2] (by decide)
                obtain ⟨w_312, hw_312⟩ := h_w312_exists
                have h_w132_exists : ∃ w, Survives setup [s1, s3, s2] w :=
                  survives_exists setup [s1, s3, s2] (by decide)
                obtain ⟨w_132, hw_132⟩ := h_w132_exists
                by_cases h_eq : w_312 = w_132
                · have h_dup : ∃ winner, Survives setup [s3, s1, s2] winner ∧ Survives setup [s1, s3, s2] winner := by
                    use w_312
                    constructor
                    · exact hw_312
                    · rw [h_eq] at hw_132; exact hw_132
                  obtain ⟨winner, hw1, hw2⟩ := h_dup
                  have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                    apply duplicate_winner_implies_count_le_five setup [s3, s1, s2] [s1, s3, s2]
                    · intro h_eq'
                      injection h_eq' with h1 h2
                      exact hs13 h1
                    · decide
                    · decide
                    · exact hw1
                    · exact hw2
                  omega
                · -- otherwise use duplication among three winners
                  have h_dup : w_123 = w_312 ∨ w_123 = w_132 ∨ w_312 = w_132 := by
                    by_contra h_all
                    push_neg at h_all
                    have : ({w_123, w_312, w_132} : Finset Student).card = 3 := by
                      have h1 : w_312 ≠ w_123 := h_all.1
                      have h2 : w_132 ≠ w_123 := h_all.2.1
                      have h3 : w_132 ≠ w_312 := h_all.2.2
                      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
                      · simp
                      · simp [h3]
                      · simp [h2]
                    -- but all winners are in S1 (finite), so contradiction with count=6
                    -- use contradiction by pigeonhole on 3 orderings
                    exact (by omega)
                  cases h_dup with
                  | inl h =>
                    have h_dup' : ∃ winner, Survives setup [s1, s2, s3] winner ∧ Survives setup [s3, s1, s2] winner := by
                      use w_123
                      constructor
                      · exact hw_123
                      · rw [h] at hw_312; exact hw_312
                    obtain ⟨winner, hw1, hw2⟩ := h_dup'
                    have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                      apply duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s3, s1, s2]
                      · intro h_eq'
                        injection h_eq' with h1 h2
                        exact hs13 h1.symm
                      · decide
                      · decide
                      · exact hw1
                      · exact hw2
                    omega
                  | inr h =>
                    cases h with
                    | inl h =>
                      have h_dup' : ∃ winner, Survives setup [s1, s2, s3] winner ∧ Survives setup [s1, s3, s2] winner := by
                        use w_123
                        constructor
                        · exact hw_123
                        · rw [h] at hw_132; exact hw_132
                      obtain ⟨winner, hw1, hw2⟩ := h_dup'
                      have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                        apply duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s1, s3, s2]
                        · intro h_eq'
                          injection h_eq' with h1 h2
                          exact hs23 h2
                        · decide
                        · decide
                        · exact hw1
                        · exact hw2
                      omega
                    | inr h =>
                      have h_dup' : ∃ winner, Survives setup [s3, s1, s2] winner ∧ Survives setup [s1, s3, s2] winner := by
                        use w_312
                        constructor
                        · exact hw_312
                        · rw [h] at hw_132; exact hw_132
                      obtain ⟨winner, hw1, hw2⟩ := h_dup'
                      have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                        apply duplicate_winner_implies_count_le_five setup [s3, s1, s2] [s1, s3, s2]
                        · intro h_eq'
                          injection h_eq' with h1 h2
                          exact hs13 h1
                        · decide
                        · decide
                        · exact hw1
                        · exact hw2
                      omega

          · -- |S3 ∩ S1| ≥ 4
            have h31_eq_4 : (S3 ∩ S1).card = 4 := by
              have : (S3 ∩ S1).card ≤ min S3.card S1.card := inter_card_le_min S3 S1
              rw [h_S3_card, h_S1_card] at this
              simp at this
              omega
            -- S3 = S1
            have h_S3_eq_S1 : S3 = S1 := eq_of_inter_card_eq_four S3 S1 h_S3_card h_S1_card h31_eq_4
            -- Similar analysis as for S1 = S2 case
            have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
              have h_le_6 := champions_le_six setup
              by_contra h_not_le_5
              push_neg at h_not_le_5
              have h_eq_6 : countPotentialChampions setup = 6 := by omega

              -- Define intermediate sets
              let U_31 := computeTopHalf setup s1 S3
              let U_13 := computeTopHalf setup s3 S1
              let U_32 := computeTopHalf setup s2 S3
              let U_12 := computeTopHalf setup s2 S1

              have h_U32_eq_U12 : U_32 = U_12 := by
                unfold U_32 U_12
                rw [h_S3_eq_S1]

              let Y := U_32
              have h_Y_card : Y.card = 2 := by
                unfold Y U_32
                exact computeTopHalf_card setup s2 S3
              have h_U31_card : U_31.card = 2 := by
                unfold U_31
                exact computeTopHalf_card setup s1 S3
              have h_U13_card : U_13.card = 2 := by
                unfold U_13
                exact computeTopHalf_card setup s3 S1

              let ord1 := [s3, s2, s1]
              let ord2 := [s1, s2, s3]
              let ord3 := [s3, s1, s2]
              let ord4 := [s1, s3, s2]

              -- Winners for ord1 and ord2 are in Y
              have h_winner1 : ∃ w ∈ Y, Survives setup ord1 w := by
                have h_surv : ∃ w, Survives setup ord1 w := survives_exists setup ord1 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                · unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw
                  exact computeTopHalf_subset setup s1 Y hw
                · exact hw

              have h_winner2 : ∃ w ∈ Y, Survives setup ord2 w := by
                have h_surv : ∃ w, Survives setup ord2 w := survives_exists setup ord2 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                · unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw
                  exact computeTopHalf_subset setup s3 Y hw
                · exact hw

              -- If U_31 ∩ Y is nonempty, winner of ord3 is in Y
              by_cases h_U31_inter : (U_31 ∩ Y).Nonempty
              · have h_winner3 : ∃ w ∈ Y, Survives setup ord3 w := by
                  have h_surv : ∃ w, Survives setup ord3 w := survives_exists setup ord3 (by decide)
                  obtain ⟨w, hw⟩ := h_surv
                  use w
                  constructor
                  · unfold Survives at hw
                    simp only [List.foldl_cons, List.foldl_nil] at hw
                    exact computeTopHalf_subset setup s2 Y hw
                  · exact hw

                obtain ⟨w1, hw1_Y, hw1_surv⟩ := h_winner1
                obtain ⟨w2, hw2_Y, hw2_surv⟩ := h_winner2
                obtain ⟨w3, hw3_Y, hw3_surv⟩ := h_winner3
                by_cases h12 : w1 = w2
                · apply duplicate_winner_implies_count_le_five setup ord1 ord2
                  · intro h_eq
                    simp only [ord1, ord2] at h_eq
                    injection h_eq
                  · decide
                  · decide
                  · exact hw1_surv
                  · rw [← h12] at hw2_surv; exact hw2_surv
                · by_cases h13 : w1 = w3
                  · apply duplicate_winner_implies_count_le_five setup ord1 ord3
                    · intro h_eq
                      simp only [ord1, ord3] at h_eq
                      injection h_eq with h1 hrest
                      injection hrest
                    · decide
                    · decide
                    · exact hw1_surv
                    · rw [← h13] at hw3_surv; exact hw3_surv
                  · have h23 : w2 = w3 := by
                      by_contra h_ne
                      have h_three : ({w1, w2, w3} : Finset Student).card = 3 := by
                        have h1 : w2 ≠ w1 := h12.symm
                        have h2 : w3 ≠ w1 := h13.symm
                        have h3 : w3 ≠ w2 := h_ne
                        rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
                        · simp
                        · simp [h3]
                        · simp [h2]
                      have : ({w1, w2, w3} : Finset Student).card ≤ Y.card := by
                        apply Finset.card_le_card
                        intro z hz
                        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
                        cases hz with
                        | inl h => rw [h]; exact hw1_Y
                        | inr h =>
                          cases h with
                          | inl h => rw [h]; exact hw2_Y
                          | inr h => rw [h]; exact hw3_Y
                      rw [h_three, h_Y_card] at this
                      omega
                    apply duplicate_winner_implies_count_le_five setup ord2 ord3
                    · intro h_eq
                      simp only [ord2, ord3] at h_eq
                      injection h_eq with h1 hrest
                      injection hrest
                    · decide
                    · decide
                    · exact hw2_surv
                    · rw [← h23] at hw3_surv; exact hw3_surv

              · -- U_31 ∩ Y = ∅, then U_31 = S3 \ Y and similarly U_13 = S1 \ Y
                have h_U31_sub : U_31 ⊆ S3 \ Y := by
                  intro z hz
                  rw [Finset.mem_sdiff]
                  constructor
                  · have : U_31 ⊆ S3 := by
                      unfold U_31
                      exact computeTopHalf_subset setup s1 S3
                    exact this hz
                  · intro hzY
                    have : z ∈ U_31 ∩ Y := ⟨hz, hzY⟩
                    have h_empty : (U_31 ∩ Y) = ∅ := by
                      rw [Finset.not_nonempty_iff_eq_empty] at h_U31_inter
                      exact h_U31_inter
                    simpa [h_empty] using this
                have h_diff_card : (S3 \ Y).card = 2 := by
                  have h_sub : Y ⊆ S3 := by
                    unfold Y U_32
                    exact computeTopHalf_subset setup s2 S3
                  have : (S3 \ Y).card = S3.card - Y.card := by
                    rw [Finset.card_sdiff h_sub]
                  rw [this, h_S3_card, h_Y_card]
                  omega
                have h_U31_eq : U_31 = S3 \ Y :=
                  Finset.eq_of_subset_of_card_le h_U31_sub (by rw [h_U31_card, h_diff_card])

                have h_U13_sub : U_13 ⊆ S1 \ Y := by
                  intro z hz
                  rw [Finset.mem_sdiff]
                  constructor
                  · have : U_13 ⊆ S1 := by
                      unfold U_13
                      exact computeTopHalf_subset setup s3 S1
                    exact this hz
                  · intro hzY
                    have : z ∈ U_13 ∩ Y := ⟨hz, hzY⟩
                    have h_empty : (U_13 ∩ Y) = ∅ := by
                      by_contra h_ne
                      have h_nonempty : (U_13 ∩ Y).Nonempty := by
                        rw [Finset.nonempty_iff_ne_empty]
                        exact h_ne
                      exact (h_U31_inter (by
                        have : U_31 = U_13 := by
                          unfold U_31 U_13
                          rw [h_S3_eq_S1]
                        simpa [this] using h_nonempty))
                    simpa [h_empty] using this
                have h_diff_card' : (S1 \ Y).card = 2 := by
                  have h_sub : Y ⊆ S1 := by
                    unfold Y U_32
                    rw [h_S3_eq_S1]
                    exact computeTopHalf_subset setup s2 S3
                  have : (S1 \ Y).card = S1.card - Y.card := by
                    rw [Finset.card_sdiff h_sub]
                  rw [this, h_S1_card, h_Y_card]
                  omega
                have h_U13_eq : U_13 = S1 \ Y :=
                  Finset.eq_of_subset_of_card_le h_U13_sub (by rw [h_U13_card, h_diff_card'])

                -- Therefore U_31 = U_13 (since S3 = S1)
                have h_U31_eq_U13 : U_31 = U_13 := by
                  rw [h_U31_eq, h_U13_eq, h_S3_eq_S1]

                have h_dup : ∃ winner, Survives setup ord3 winner ∧ Survives setup ord4 winner := by
                  have h_surv : ∃ w, Survives setup ord3 w := survives_exists setup ord3 (by decide)
                  obtain ⟨w, hw⟩ := h_surv
                  use w
                  constructor
                  · exact hw
                  · unfold Survives at hw ⊢
                    simp only [List.foldl_cons, List.foldl_nil] at hw ⊢
                    rw [h_U31_eq_U13]
                    exact hw
                obtain ⟨winner, hw1, hw2⟩ := h_dup
                have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
                  apply duplicate_winner_implies_count_le_five setup ord3 ord4
                  · intro h_eq
                    simp only [ord3, ord4] at h_eq
                    injection h_eq with h1 h2
                    exact hs13 h1
                  · decide
                  · decide
                  · exact hw1
                  · exact hw2
                omega

            exact h_count_le_5

        exact h_count_le_5

/-- 核心定理：最大潜在冠军数为 5 -/
theorem problem_statement : ∃ n, IsMaxPotentialChampions n := by
  use 5
  constructor
  · -- Prove ∀ setup, count ≤ 5
    intros Student Subject _ _ _ _ setup
    exact champions_le_five setup
  · -- Prove ∃ setup, count = 5
    use (Fin 8), (Fin 3), inferInstance, inferInstance, inferInstance, inferInstance
    use exampleSetup
    exact example_count

/-- 题目 1.1 的最终陈述（与 problem_statement 等价） -/
theorem prob1_1 : ∃ n, IsMaxPotentialChampions n := by
  exact problem_statement

end
end CompetitionSetup
