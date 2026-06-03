
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

  (score : Subject → Student → ℕ)

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


  have hx_take : x ∈ sorted.take k := hx
  have hy_current : y ∈ current := hy.1
  have hy_not_take : y ∉ sorted.take k := hy.2


  haveI : Std.Total (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
    ⟨by intro a b; exact le_total _ _⟩
  haveI : IsTrans Student (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
    ⟨by intro a b c hab hbc; exact le_trans hbc hab⟩
  have h_pairwise : sorted.Pairwise (fun a b => setup.score sub a ≥ setup.score sub b) := by
    simpa [sorted] using
      (List.pairwise_mergeSort' (r := fun a b => setup.score sub a ≥ setup.score sub b) current.toList)


  have hy_sorted : y ∈ sorted := by
    have h_perm := List.mergeSort_perm current.toList (fun a b => decide (setup.score sub a ≥ setup.score sub b))
    have : y ∈ current.toList := Finset.mem_toList.mpr hy_current
    exact (List.Perm.mem_iff h_perm.symm).1 this


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


  by_cases h_eq : i = j
  ·
    subst h_eq
    have hxy : x = y := by
      simpa [hxi] using hyj
    simpa [hxy]
  ·
    have hij : i < j ∨ j < i := Nat.lt_or_gt_of_ne h_eq
    cases hij with
    | inl hij =>

      have : setup.score sub (sorted[i]) ≥ setup.score sub (sorted[j]) := by
        have h_rel := List.pairwise_iff_get.mp h_pairwise
        exact h_rel ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hxy : setup.score sub x ≥ setup.score sub y := by
        simpa [hxi, hyj] using this
      exact hxy
    | inr hji =>

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

    | 0, 0 => 7 | 0, 1 => 6 | 0, 2 => 4 | 0, 3 => 8 | 0, 4 => 3 | 0, 5 => 5 | 0, 6 => 2 | 0, 7 => 1

    | 1, 0 => 6 | 1, 1 => 5 | 1, 2 => 2 | 1, 3 => 1 | 1, 4 => 4 | 1, 5 => 3 | 1, 6 => 8 | 1, 7 => 7

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



/-- 辅助引理：幸存者集合的大小为4 -/
lemma survivalSet_card (setup : CompetitionSetup Student Subject) (sub : Subject) :
    (survivalSet setup sub).card = 4 := by
  unfold survivalSet computeTopHalf





  have h_univ_card : (univ : Finset Student).card = 8 := setup.student_count
  have h_list_len : (univ : Finset Student).toList.length = 8 := by
    rw [Finset.length_toList, h_univ_card]
  have h_sorted_len : ((univ : Finset Student).toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))).length = 8 := by
    rw [List.length_mergeSort, h_list_len]
  have h_take_len : (((univ : Finset Student).toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))).take ((univ : Finset Student).card / 2)).length = 4 := by
    rw [List.length_take, h_sorted_len, h_univ_card]
    norm_num


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

    have h_count : (univ.filter (fun t => setup.score sub t > setup.score sub s)).card ≤ 3 := by omega

    have h_univ_card : (univ : Finset Student).card = 8 := setup.student_count
    have hk : (univ : Finset Student).card / 2 = 4 := by
      simpa [h_univ_card]
    have hk' : (Fintype.card Student) / 2 = 4 := by
      simpa [setup.student_count]
    have h_s_in_univ : s ∈ (univ : Finset Student) := Finset.mem_univ s


    let sorted := (univ : Finset Student).toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))


    have h_s_in_list : s ∈ (univ : Finset Student).toList := by
      rw [Finset.mem_toList]
      exact h_s_in_univ


    have h_s_in_sorted : s ∈ sorted := by
      rw [mem_mergeSort_iff]
      exact h_s_in_list



    by_contra h_not_in_take


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


    haveI : Std.Total (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
      ⟨by intro a b; exact le_total _ _⟩
    haveI : IsTrans Student (fun a b : Student => setup.score sub a ≥ setup.score sub b) :=
      ⟨by intro a b c hab hbc; exact le_trans hbc hab⟩
    have h_pairwise : sorted.Pairwise (fun a b => setup.score sub a ≥ setup.score sub b) := by
      simpa [sorted] using
        (List.pairwise_mergeSort' (r := fun a b => setup.score sub a ≥ setup.score sub b)
          (univ : Finset Student).toList)



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


    have h_take_nodup : (sorted.take 4).Nodup := by
      apply List.nodup_take_of_nodup
      have h_perm := List.mergeSort_perm (univ : Finset Student).toList (fun a b => decide (setup.score sub a ≥ setup.score sub b))
      exact (List.Perm.nodup_iff h_perm).mpr (Finset.nodup_toList univ)


    have h_all_greater : ∀ t ∈ sorted.take 4, setup.score sub t > setup.score sub s := by
      intro t ht
      have ht_fin : t ∈ computeTopHalf setup sub (univ : Finset Student) := by
        unfold computeTopHalf
        simpa [hk'] using (List.mem_toFinset.mpr ht)
      have hs_not :
          s ∈ (univ : Finset Student) \ computeTopHalf setup sub (univ : Finset Student) := by
        refine Finset.mem_sdiff.mpr ?_
        refine ⟨Finset.mem_univ s, ?_⟩

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

    rw [List.mem_toFinset] at h_in_survival


    let sorted := (univ : Finset Student).toList.mergeSort (fun a b => decide (setup.score sub a ≥ setup.score sub b))


    have h_pairwise : sorted.Pairwise (fun a b => setup.score sub a > setup.score sub b) := by
      simpa [sorted] using
        (List.pairwise_mergeSort' (r := fun a b => setup.score sub a > setup.score sub b)
          (univ : Finset Student).toList)



    have h_take_len : (sorted.take 4).length = 4 := by
      rw [List.length_take]
      have : sorted.length = 8 := by
        rw [List.length_mergeSort]
        have : (univ : Finset Student).toList.length = 8 := by
          rw [Finset.length_toList, setup.student_count]
        exact this
      rw [this]
      norm_num


    have h_s_idx : ∃ i, i < 4 ∧ sorted.take 4[i]? = some s := by
      have : s ∈ sorted.take 4 := h_in_survival
      obtain ⟨i, hi, hs⟩ := List.mem_iff_getElem.mp this
      use i
      constructor
      · calc i < sorted.take 4.length := hi
          _ = 4 := h_take_len
      · rw [List.getElem?_eq_getElem hi]
        simp [hs]


    obtain ⟨i, hi, hs_at_i⟩ := h_s_idx


    have h_greater_in_prefix : ∀ t ∈ univ, setup.score sub t > setup.score sub s →
        ∃ j, j < i ∧ sorted.take 4[j]? = some t := by
      intro t ht_univ ht_greater

      have ht_in_sorted : t ∈ sorted := by
        rw [mem_mergeSort_iff]
        rw [Finset.mem_toList]
        exact ht_univ

      by_cases ht_in_take : t ∈ sorted.take 4
      ·
        obtain ⟨j, hj, ht_at_j⟩ := List.mem_iff_getElem.mp ht_in_take
        use j
        constructor
        ·

          by_contra h_not_lt
          push_neg at h_not_lt

          have : i ≤ j := h_not_lt


          have h_s_at_i_full : sorted.take 4[i] = s := by
            have : sorted.take 4[i]? = some s := hs_at_i
            cases h_eq : sorted.take 4[i]?
            · simp at this
            · simp at this
              rw [h_eq] at this
              simp at this
              exact this
          have h_t_at_j_full : sorted.take 4[j] = t := ht_at_j

          have h_take_pairwise : (sorted.take 4).Pairwise (fun a b => setup.score sub a > setup.score sub b) := by
            exact List.Pairwise.take _ h_pairwise
          have : setup.score sub (sorted.take 4[i]) > setup.score sub (sorted.take 4[j]) := by
            apply List.Pairwise.rel_get_of_lt h_take_pairwise
            constructor
            · exact hi
            · calc i < j := by omega
                _ < sorted.take 4.length := hj
          rw [h_s_at_i_full, h_t_at_j_full] at this

          omega
        · rw [List.getElem?_eq_getElem hj]
          simp [ht_at_j]
      ·
        have ht_in_drop : t ∈ sorted.drop 4 := by
          have h_sorted_eq : sorted = sorted.take 4 ++ sorted.drop 4 := List.take_append_drop 4 sorted
          have : t ∈ sorted.take 4 ∨ t ∈ sorted.drop 4 := by
            rw [←h_sorted_eq] at ht_in_sorted
            exact List.mem_append.mp ht_in_sorted
          cases this with
          | inl h => contradiction
          | inr h => exact h


        have : setup.score sub s > setup.score sub t := by
          exact List.Pairwise.rel_of_mem_take_of_mem_drop h_pairwise h_in_survival ht_in_drop

        omega


    have : (univ.filter (fun t => setup.score sub t > setup.score sub s)).card ≤ i := by


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


  ext x
  constructor
  ·
    intro hx
    by_contra hx_not_t

    have hx_in_s : x ∈ s := by
      have : x ∈ sorted := by
        rw [List.mem_toFinset] at hx
        exact List.mem_of_mem_take hx
      have : x ∈ s.toList := (List.Perm.mem_iff h_perm).1 this
      exact Finset.mem_toList.mp this
    have hx_in_sdiff : x ∈ s \ t := Finset.mem_sdiff.mpr ⟨hx_in_s, hx_not_t⟩


    rw [List.mem_toFinset, List.mem_take] at hx
    obtain ⟨i, hi_lt_k, hi_lt, hxi⟩ := hx
    have hxi' : sorted[i] = x := by
      simpa using hxi


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

        have hk : t.card = k := by simpa [ht_card]

        have := congrArg (fun n => n - t_before_i.card) h_partition

        simp [Nat.add_sub_cancel_left, hk] at this
        exact this

      have h_le : t_before_i.card ≤ i := h_t_before_card
      have h_sub_le : k - i ≤ k - t_before_i.card := Nat.sub_le_sub_left h_le _

      exact h_diff ▸ h_sub_le


    have : k - i ≥ 1 := by
      have : i < k := hi_lt_k
      exact Nat.succ_le_iff.mp (Nat.sub_pos_of_lt this)
    have h_exists_t_after_i :
        ∃ y ∈ t, ∃ j, i ≤ j ∧ ∃ hj_lt : j < sorted.length, sorted.get ⟨j, hj_lt⟩ = y := by

      have : (t \ t_before_i).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h_empty
        have : (t \ t_before_i).card = 0 := by simp [h_empty]
        omega
      obtain ⟨y, hy⟩ := this
      use y
      constructor
      · exact Finset.mem_of_mem_sdiff hy
      ·
        have hy_in_sorted : y ∈ sorted := by
          exact (List.Perm.mem_iff h_perm).2 (by
            simpa [Finset.mem_toList] using ht_sub (Finset.mem_of_mem_sdiff hy))
        obtain ⟨j, hj, hyj⟩ := List.mem_iff_getElem.mp hy_in_sorted
        use j
        constructor
        ·
          by_contra hj_lt_i
          push_neg at hj_lt_i

          have : y ∈ sorted.take i := by
            refine (List.mem_iff_getElem).2 ?_
            refine ⟨j, ?_, ?_⟩
            ·
              have : j < min i sorted.length := lt_min_iff.mpr ⟨hj_lt_i, hj⟩
              simpa [List.length_take] using this
            · simpa [List.getElem_take] using hyj

          have : y ∈ t_before_i := by
            simp [t_before_i, Finset.mem_inter, List.mem_toFinset, this]
            exact Finset.mem_of_mem_sdiff hy

          exact Finset.not_mem_sdiff_of_mem this hy
        · exact ⟨hj, hyj⟩

    obtain ⟨y, hy_in_t, j, hj_ge_i, hj_lt, hyj⟩ := h_exists_t_after_i





    have h_score_y_gt_x : score y > score x := h_scores y hy_in_t x hx_in_sdiff



    by_cases h_j_eq_i : j = i
    ·
      subst h_j_eq_i
      have hxi' : sorted.get ⟨j, hj_lt⟩ = x := by
        simpa using hxi
      have : x = y := by
        rw [← hxi', ← hyj]

      rw [this] at hx_in_sdiff
      exact Finset.not_mem_sdiff_of_mem hy_in_t hx_in_sdiff
    ·
      have hj_gt_i : i < j := lt_of_le_of_ne hj_ge_i (Ne.symm h_j_eq_i)
      have h_sorted_order : score (sorted.get ⟨i, hi_lt⟩) ≥ score (sorted.get ⟨j, hj_lt⟩) := by
        have hj_fin : (⟨i, hi_lt⟩ : Fin sorted.length) < ⟨j, hj_lt⟩ := by
          simpa using hj_gt_i
        exact List.Pairwise.rel_get_of_lt h_sorted hj_fin
      rw [hxi, hyj] at h_sorted_order

      omega

  ·
    intro hx_in_t
    rw [List.mem_toFinset, List.mem_take]


    have hx_in_sorted : x ∈ sorted := by
      exact (List.Perm.mem_iff h_perm).2 (by
        simpa [Finset.mem_toList] using ht_sub hx_in_t)


    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx_in_sorted
    use i
    constructor
    ·
      by_contra hi_ge_k
      push_neg at hi_ge_k


      have h_count_t : (sorted.filter (fun y => y ∈ t)).length = k :=
        count_subset_in_perm s t sorted k ht_sub ht_card h_perm


      let t_in_first_k := (sorted.take k).filter (fun y => decide (y ∈ t))


      let t_after_k := (sorted.drop k).filter (fun y => decide (y ∈ t))


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


      have hx_in_after : x ∈ t_after_k := by
        simp [t_after_k, List.mem_filter]
        constructor
        ·
          refine (List.mem_iff_getElem).2 ?_
          refine ⟨i - k, ?_, ?_⟩
          ·
            have hi_lt_len : i < sorted.length := hi
            have hk_le_i : k ≤ i := hi_ge_k
            have : i - k < sorted.length - k := by
              omega
            have hi_drop : i - k < (sorted.drop k).length := by
              simpa [List.length_drop] using this
            exact hi_drop
          ·
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


      have h_after_pos : t_after_k.length ≥ 1 := by
        have h_ne : t_after_k ≠ [] := List.ne_nil_of_mem hx_in_after
        have hpos : 0 < t_after_k.length := List.length_pos_of_ne_nil h_ne
        exact Nat.succ_le_iff.mpr hpos


      have h_first_k_count : t_in_first_k.length ≤ k - 1 := by
        have h_le : t_in_first_k.length + 1 ≤ k := by
          have := Nat.add_le_add_left h_after_pos t_in_first_k.length

          simpa [h_partition] using this
        exact Nat.le_sub_of_add_le h_le










      have h_sdiff_in_first_k : ∃ y, y ∈ (sorted.take k) ∧ y ∈ s \ t := by

        have h_take_length : (sorted.take k).length = k := by
          rw [List.length_take, h_length]
          simp [hs_card]


        by_contra h_none
        push_neg at h_none

        have : ∀ y ∈ sorted.take k, y ∈ t := by
          intro y hy
          have hy_in_s : y ∈ s := by
            have : y ∈ sorted := List.mem_of_mem_take hy
            have : y ∈ s.toList := (List.Perm.mem_iff h_perm).1 this
            exact Finset.mem_toList.mp this
          by_contra hy_not_t
          have : y ∈ s \ t := Finset.mem_sdiff.mpr ⟨hy_in_s, hy_not_t⟩
          exact h_none y hy this

        have : t_in_first_k.length = k := by
          have h_all_in_t : ∀ y ∈ sorted.take k, y ∈ t := this


          unfold t_in_first_k
          have : (sorted.take k).filter (fun y => decide (y ∈ t)) = sorted.take k := by
            apply List.filter_eq_self.2
            intro y hy
            have hy_t : y ∈ t := h_all_in_t y hy
            simpa using hy_t
          rw [this, h_take_length]
        omega

      obtain ⟨y, hy_in_take, hy_in_sdiff⟩ := h_sdiff_in_first_k



      obtain ⟨j, hj_lt_k, hj_lt_len, hyj⟩ := (List.mem_take).1 hy_in_take
      have hyj' : sorted.get ⟨j, hj_lt_len⟩ = y := by
        simpa using hyj



      have h_score_x_gt_y : score x > score y := h_scores x hx_in_t y hy_in_sdiff


      have h_sorted_order : score (sorted.get ⟨j, hj_lt_len⟩) ≥ score (sorted.get ⟨i, hi⟩) := by
        have h_rel := List.pairwise_iff_get.mp h_sorted
        have hj_lt_i : j < i := Nat.lt_of_lt_of_le hj_lt_k hi_ge_k
        exact h_rel ⟨j, hj_lt_len⟩ ⟨i, hi⟩ hj_lt_i


      have : sorted.get ⟨j, hj_lt_len⟩ = y := hyj'
      have : sorted.get ⟨i, hi⟩ = x := hxi


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

  have hx_in_s : x ∈ s := by
    have : x ∈ sorted := by
      rw [List.mem_toFinset] at hx
      exact List.mem_of_mem_take hx
    have h_perm := List.mergeSort_perm s.toList (fun a b => decide (score a ≥ score b))
    have : x ∈ s.toList := (List.Perm.mem_iff h_perm).1 this
    exact Finset.mem_toList.mp this
  have hx_in_sdiff : x ∈ s \ t := Finset.mem_sdiff.mpr ⟨hx_in_s, hx_not_t⟩


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


  have h_t_count : k ≤ (sorted.filter (fun y => y ∈ t)).length := by
    have : (sorted.filter (fun y => y ∈ t)).length = t.card := by
      have h_count := count_subset_in_perm s t sorted t.card ht_sub rfl h_perm
      exact h_count
    simpa [this] using ht_card


  have h_exists_t_after_i :
      ∃ y ∈ t, ∃ j, j ≥ i ∧ j < sorted.length ∧ sorted[j]? = some y := by

    let t_before_i := (sorted.take i).filter (fun y => y ∈ t)
    have h_before_count : t_before_i.length ≤ i := by
      unfold t_before_i
      have h_le_take : t_before_i.length ≤ (sorted.take i).length := List.length_filter_le _ _
      have h_take_le : (sorted.take i).length ≤ i := by
        simpa [List.length_take] using (Nat.min_le_left i sorted.length)
      exact le_trans h_le_take h_take_le


    let t_in_sorted := sorted.filter (fun y => y ∈ t)
    have h_t_count_internal : t_in_sorted.length = t.card := by
      unfold t_in_sorted
      exact count_subset_in_perm s t sorted t.card ht_sub rfl h_perm


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


    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ h_after_nonempty

    use y
    constructor
    ·
      have : y ∈ t_after_i := hy
      unfold t_after_i at this
      have h_mem : y ∈ sorted.drop i ∧ y ∈ t := by
        simpa [List.mem_filter] using this
      exact h_mem.2
    ·
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
      ·
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



  have h_score_y_gt_x : score y > score x := h_scores y hy_in_t x hx_in_sdiff


  by_cases h_j_eq_i : j = i
  ·
    have hj_lt' : i < sorted.length := by simpa [h_j_eq_i] using hj_lt
    have hyj' : sorted[i] = y := by
      simpa [h_j_eq_i, List.getElem?_eq_getElem hj_lt'] using hyj
    have : x = y := by
      calc
        x = sorted[i] := hxi_sorted.symm
        _ = y := hyj'
    rw [this] at hx_not_t
    exact hx_not_t hy_in_t
  ·
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


  let I := S1 ∩ S2












  unfold Survives
  simp only []


  let S0 := (univ : Finset Student)
  let S1_round1 := computeTopHalf setup s1 S0
  let S1_round2 := computeTopHalf setup s2 S1_round1
  let S1_round3 := computeTopHalf setup s3 S1_round2


  let S2_round1 := computeTopHalf setup s2 S0
  let S2_round2 := computeTopHalf setup s1 S2_round1
  let S2_round3 := computeTopHalf setup s3 S2_round2


















  have h_S1_round1 : S1_round1 = S1 := by
    unfold S1_round1 S1 survivalSet
    rfl







  have h_I_in_S2 : I ⊆ S2 := Finset.inter_subset_right
  have h_I_in_S1 : I ⊆ S1 := Finset.inter_subset_left

  have h_S1_diff_not_in_S2 : ∀ x ∈ S1 \ I, x ∉ S2 := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    intro hx_in_S2
    have : x ∈ I := Finset.mem_inter.mpr ⟨hx.1, hx_in_S2⟩
    exact hx.2 this




  have h_I_better_s2 : ∀ u ∈ I, ∀ v ∈ S1 \ I, setup.score s2 u > setup.score s2 v := by
    intro u hu v hv
    have hu_in_S2 : u ∈ S2 := h_I_in_S2 hu
    have hv_not_S2 : v ∉ S2 := h_S1_diff_not_in_S2 v hv

    have hu_rank : rank setup s2 u ≤ 4 :=
      (rank_le_four_iff_in_survival setup s2 u).2 hu_in_S2

    have hv_rank : rank setup s2 v > 4 := by
      exact not_in_survival_implies_rank_gt_four setup s2 v hv_not_S2

    unfold rank at hu_rank hv_rank





    by_contra h_not_greater
    push_neg at h_not_greater

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






  have h_S1_card : S1.card = 4 := by
    simpa [S1] using (survivalSet_card setup s1)

  have h_I_card : I.card = 2 := h_inter_2


  have h_S1_round2_eq_I : S1_round2 = I := by
    unfold S1_round2
    rw [h_S1_round1]

    have h_apply := top_k_equals_high_score_subset S1 I (setup.score s2) 2
      (Finset.inter_subset_left) h_I_card (by omega : 2 ≤ S1.card) h_I_better_s2
    simpa [computeTopHalf, h_S1_card] using h_apply


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

    have h_apply := top_k_equals_high_score_subset S2 I (setup.score s1) 2
      (Finset.inter_subset_right) h_I_card (by omega : 2 ≤ S2.card) h_I_better_s1
    have h_S2_card : S2.card = 4 := by
      simpa [S2] using (survivalSet_card setup s2)
    simpa [computeTopHalf, h_S2_card] using h_apply


  have h_final_eq : S1_round3 = S2_round3 := by
    unfold S1_round3 S2_round3
    rw [h_S1_round2_eq_I, h_S2_round2_eq_I]


  have h_I_nonempty : I.Nonempty := by
    have : 0 < I.card := by
      simpa [h_I_card] using (Nat.succ_pos 1)
    exact Finset.card_pos.mp this



  have h_S1_round3_card : S1_round3.card = 1 := by
    unfold S1_round3
    rw [h_S1_round2_eq_I]
    simpa [h_I_card] using (computeTopHalf_card setup s3 I)

  have h_S1_round3_nonempty : S1_round3.Nonempty := by
    have : 0 < S1_round3.card := by
      simpa [h_S1_round3_card] using (Nat.succ_pos 0)
    exact Finset.card_pos.mp this


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



  have union_bound : (S1 ∪ S2 ∪ S3).card ≤ 8 := by
    have : S1 ∪ S2 ∪ S3 ⊆ univ := Finset.subset_univ _
    calc (S1 ∪ S2 ∪ S3).card
        ≤ univ.card := Finset.card_le_card this
      _ = 8 := hU




  have union_12 : (S1 ∪ S2).card = S1.card + S2.card - (S1 ∩ S2).card := by
    have h' : (S1 ∪ S2).card + (S1 ∩ S2).card = S1.card + S2.card := by
      simpa using (Finset.card_union_add_card_inter S1 S2)
    exact Nat.eq_sub_of_add_eq h'


  have union_123 : (S1 ∪ S2 ∪ S3).card = (S1 ∪ S2).card + S3.card - ((S1 ∪ S2) ∩ S3).card := by
    have h' : (S1 ∪ S2 ∪ S3).card + ((S1 ∪ S2) ∩ S3).card = (S1 ∪ S2).card + S3.card := by
      simpa [Finset.union_assoc] using (Finset.card_union_add_card_inter (S1 ∪ S2) S3)
    exact Nat.eq_sub_of_add_eq h'


  have inter_dist : (S1 ∪ S2) ∩ S3 = (S1 ∩ S3) ∪ (S2 ∩ S3) := by
    ext x
    simp [Finset.mem_inter, Finset.mem_union]
    tauto


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


  have key_eq : (S1 ∪ S2 ∪ S3).card =
      S1.card + S2.card + S3.card - (S1 ∩ S2).card - (S1 ∩ S3).card - (S2 ∩ S3).card + (S1 ∩ S2 ∩ S3).card := by
    nlinarith [union_123, union_12, inter_card]


  have intersection_sum : (S1 ∩ S2).card + (S2 ∩ S3).card + (S3 ∩ S1).card =
      S1.card + S2.card + S3.card - (S1 ∪ S2 ∪ S3).card + (S1 ∩ S2 ∩ S3).card := by
    have : (S3 ∩ S1).card = (S1 ∩ S3).card := by
      congr 1
      ext x
      simp [Finset.mem_inter]
      tauto
    rw [this]
    nlinarith [key_eq]


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





  unfold Survives at h_surv


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

  simp at h_surv






  refine (List.mem_flatMap).2 ?_
  refine ⟨[s1, s2, s3], ?_, ?_⟩

  ·
    apply List.mem_filter.mpr
    constructor
    ·
      rw [List.mem_permutations]

      rw [← h_ord]
      exact h_perm
    ·
      simp

  ·


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



  have h_le_6 := champions_le_six setup
  by_contra h_not_le_5
  push_neg at h_not_le_5
  have h_eq_6 : countPotentialChampions setup = 6 := by omega





  have h_winner_mem : winner ∈ getChampions setup := by
    apply survives_mem_getChampions setup ord1 winner h_perm1 h_surv1





  unfold countPotentialChampions getChampions at h_eq_6


  let survivors := ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))).flatMap (fun p =>
    match p with
    | [s1', s2', s3'] =>
        let S0 := (univ : Finset Student)
        let S1 := computeTopHalf setup s1' S0
        let S2 := computeTopHalf setup s2' S1
        let S3 := computeTopHalf setup s3' S2
        S3.toList
    | _ => [])


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




  rw [h_ord1_eq] at h_surv1
  rw [h_ord2_eq] at h_surv2

  unfold Survives at h_surv1 h_surv2
  simp at h_surv1 h_surv2




  have h_winner_in_ord1_contrib : winner ∈ (match [s1, s2, s3] with
    | [s1', s2', s3'] =>
        let S0 := (univ : Finset Student)
        let S1 := computeTopHalf setup s1' S0
        let S2 := computeTopHalf setup s2' S1
        let S3 := computeTopHalf setup s3' S2
        S3.toList
    | _ => []) := by
    simpa [Finset.mem_toList] using h_surv1


  have h_winner_in_ord2_contrib : winner ∈ (match [s1', s2', s3'] with
    | [s1'', s2'', s3''] =>
        let S0 := (univ : Finset Student)
        let S1 := computeTopHalf setup s1'' S0
        let S2 := computeTopHalf setup s2'' S1
        let S3 := computeTopHalf setup s3'' S2
        S3.toList
    | _ => []) := by
    simpa [Finset.mem_toList] using h_surv2


  rw [← h_ord1_eq] at h_ord1_mem h_winner_in_ord1_contrib
  rw [← h_ord2_eq] at h_ord2_mem h_winner_in_ord2_contrib

  have h_winner_from_ord1 : winner ∈ survivors := by
    apply List.mem_flatMap_of_mem h_ord1_mem
    exact h_winner_in_ord1_contrib

  have h_winner_from_ord2 : winner ∈ survivors := by
    apply List.mem_flatMap_of_mem h_ord2_mem
    exact h_winner_in_ord2_contrib





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





  have h_count_ge_2 : List.count winner survivors ≥ 2 := by
    rw [h_count_eq]




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



















    let f := fun p => List.count winner (match p with
      | [s1', s2', s3'] =>
          let S0 := (univ : Finset Student)
          let S1 := computeTopHalf setup s1' S0
          let S2 := computeTopHalf setup s2' S1
          let S3 := computeTopHalf setup s3' S2
          S3.toList
      | _ => [])











    have h_ord1_term : f ord1 ≤ (((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))).map f).sum := by
      apply List.single_le_sum
      · intro x hx

        omega
      · exact h_ord1_mem

    have h_ord2_term : f ord2 ≤ (((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))).map f).sum := by
      apply List.single_le_sum
      · intro x hx
        omega
      · exact h_ord2_mem









    calc List.sum (List.map f ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3))))
        ≥ f ord1 + f ord2 := by












          let list := ((univ : Finset Subject).toList.permutations.filter (fun l => decide (l.length = 3)))


          have h_list_nodup : list.Nodup := by
            apply List.nodup_filter
            exact List.nodup_permutations (Finset.nodup_toList _)


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


          have h_ord1_in_finset : ord1 ∈ list.toFinset := by
            rw [List.mem_toFinset]
            exact h_ord1_mem

          have h_ord2_in_finset : ord2 ∈ list.toFinset := by
            rw [List.mem_toFinset]
            exact h_ord2_mem

          apply Finset.add_le_sum
          · intro x hx

            omega
          · exact h_ord1_in_finset
          · exact h_ord2_in_finset
          · exact h_diff
      _ ≥ 1 + 1 := by
          have : f ord1 ≥ 1 := h_count_ord1
          have : f ord2 ≥ 1 := h_count_ord2
          omega
      _ = 2 := by norm_num


  have h_winner_dup : winner ∈+ survivors := by
    rw [List.duplicate_iff_two_le_count]
    exact h_count_ge_2


  have h_not_nodup : ¬survivors.Nodup := by
    intro h_nodup
    have := List.nodup_iff_count_le_one.mp h_nodup winner
    omega


  have h_card_lt : survivors.toFinset.card < survivors.length := by
    have h_le := List.toFinset_card_le survivors
    by_contra h_not_lt
    push_neg at h_not_lt
    have h_eq : survivors.toFinset.card = survivors.length := by omega
    have := List.toFinset_card_of_nodup h_not_nodup
    rw [h_eq] at this
    exact absurd this h_not_nodup











  have h_tofinset_eq : survivors.toFinset = getChampions setup := by
    unfold survivors getChampions
    rfl

  rw [h_tofinset_eq] at h_card_lt
  unfold countPotentialChampions at h_eq_6
  rw [← h_tofinset_eq] at h_eq_6


  have : 6 < survivors.length := by
    rw [← h_eq_6]
    exact h_card_lt




















  omega

/-- 引理：证明上界为5 -/
lemma champions_le_five (setup : CompetitionSetup Student Subject) :
    countPotentialChampions setup ≤ 5 := by
  have h6 := champions_le_six setup



  by_contra h_not_le_5
  push_neg at h_not_le_5
  have h_eq_6 : countPotentialChampions setup = 6 := by omega




  obtain ⟨s1, s2, s3, hs12, hs23, hs13, huniv⟩ :=
    exists_three_distinct_of_card_eq_three setup.subject_count


  let S1 := survivalSet setup s1
  let S2 := survivalSet setup s2
  let S3 := survivalSet setup s3


  have h_S1_card : S1.card = 4 := survivalSet_card setup s1
  have h_S2_card : S2.card = 4 := survivalSet_card setup s2
  have h_S3_card : S3.card = 4 := survivalSet_card setup s3

  have h_inter_bound : (S1 ∩ S2).card + (S2 ∩ S3).card + (S3 ∩ S1).card ≥ 4 := by
    exact intersection_lower_bound Student setup.student_count S1 S2 S3 h_S1_card h_S2_card h_S3_card


  have h_exists_ge_two : (S1 ∩ S2).card ≥ 2 ∨ (S2 ∩ S3).card ≥ 2 ∨ (S3 ∩ S1).card ≥ 2 := by
    exact exists_intersection_ge_two_of_sum_ge_four S1 S2 S3 h_inter_bound


  refine (Or.elim h_exists_ge_two ?h12 ?hrest)
  · intro h12


    by_cases h12_eq_2 : (S1 ∩ S2).card = 2
    ·

      obtain ⟨winner, hw1, hw2⟩ := size_two_intersection_property setup s1 s2 s3 hs12 hs23 hs13 h12_eq_2








      have h_count_le_5 : countPotentialChampions setup ≤ 5 := by

        refine duplicate_winner_implies_count_le_five setup [s1,s2,s3] [s2,s1,s3] ?_ ?_ ?_ winner hw1 hw2
        ·
          intro h_eq
          injection h_eq with h1 h2
          exact hs12 h1
        ·

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
        ·

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
    ·
      have h12_ge_3 : (S1 ∩ S2).card ≥ 3 := by omega

      by_cases h12_eq_3 : (S1 ∩ S2).card = 3
      ·


        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          have h_le_6 := champions_le_six setup
          by_contra h_not_le_5
          push_neg at h_not_le_5
          have h_eq_6 : countPotentialChampions setup = 6 := by omega


          let I := S1 ∩ S2
          have h_I_card : I.card = 3 := h12_eq_3


          let U_12 := computeTopHalf setup s2 S1
          let U_21 := computeTopHalf setup s1 S2


          have h_U12_subset_I : U_12 ⊆ I := by

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


          have h_exists_not_U12 : ∃ x ∈ I, x ∉ U_12 := by
            by_contra h_not
            push_neg at h_not
            have : I ⊆ U_12 := h_not
            have : I.card ≤ U_12.card := Finset.card_le_card this
            rw [h_I_card, h_U12_card] at this
            omega


          have h_exists_not_U21 : ∃ x ∈ I, x ∉ U_21 := by
            by_contra h_not
            push_neg at h_not
            have : I ⊆ U_21 := h_not
            have : I.card ≤ U_21.card := Finset.card_le_card this
            rw [h_I_card, h_U21_card] at this
            omega


          let U_23 := computeTopHalf setup s3 S2
          have h_S2_card : S2.card = 4 := by
            simpa [S2] using (survivalSet_card setup s2)
          have h_U23_card : U_23.card = 2 := by
            simpa [h_S2_card] using (computeTopHalf_card setup s3 S2)











          by_cases h_U12_eq_U21 : U_12 = U_21
          ·
            have h_dup : ∃ winner, Survives setup [s1, s2, s3] winner ∧ Survives setup [s2, s1, s3] winner := by
              have h_surv1 : ∃ w, Survives setup [s1, s2, s3] w := survives_exists setup [s1, s2, s3] (by decide)
              obtain ⟨w, hw⟩ := h_surv1
              use w
              constructor
              · exact hw
              ·
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
          ·


            have h_I_nonempty : I.Nonempty := by
              rw [Finset.card_pos]
              rw [h_I_card]
              omega


            have h_exists_best : ∃ x ∈ I, ∀ z ∈ I, setup.score s3 z ≤ setup.score s3 x := by
              exact Finset.exists_max_image I (setup.score s3) h_I_nonempty

            obtain ⟨x, hx_I, hx_best⟩ := h_exists_best


            have h_I_subset_S2 : I ⊆ S2 := Finset.inter_subset_right

            have hx_in_U23 : x ∈ U_23 := by
              unfold U_23










              have h_better_count : (S2.filter (fun y => setup.score s3 y > setup.score s3 x)).card ≤ 1 := by

                have h_I_minus_x : ∀ y ∈ I, y ≠ x → setup.score s3 y ≤ setup.score s3 x := by
                  intro y hy hne
                  have := hx_best y hy
                  exact this


                have h_better_in_diff : S2.filter (fun y => setup.score s3 y > setup.score s3 x) ⊆ S2 \ I := by
                  intro y hy
                  rw [Finset.mem_filter] at hy
                  rw [Finset.mem_sdiff]
                  constructor
                  · exact hy.1
                  · intro hy_I
                    have : setup.score s3 y ≤ setup.score s3 x := hx_best y hy_I
                    omega


                have h_diff_card : (S2 \ I).card ≤ 1 := by
                  have : (S2 \ I).card = S2.card - I.card := by
                    rw [Finset.card_sdiff h_I_subset_S2]
                  rw [this, h_S2_card, h_I_card]
                  omega

                have := Finset.card_le_card h_better_in_diff
                omega



















              have hx_in_S2 : x ∈ S2 := h_I_subset_S2 hx_I
              apply at_most_k_minus_1_better_implies_in_top_k setup s3 S2 x 2
              · exact hx_in_S2
              · omega
              · rw [h_S2_card]; omega
              · exact h_better_count


            have h_w231_exists : ∃ w, Survives setup [s2, s3, s1] w := survives_exists setup [s2, s3, s1] (by decide)
            obtain ⟨w_231, hw_231⟩ := h_w231_exists

            by_cases h_w231_eq_x : w_231 = x
            ·






              have h_w123_exists : ∃ w, Survives setup [s1, s2, s3] w := survives_exists setup [s1, s2, s3] (by decide)
              obtain ⟨w_123, hw_123⟩ := h_w123_exists

              have h_w213_exists : ∃ w, Survives setup [s2, s1, s3] w := survives_exists setup [s2, s1, s3] (by decide)
              obtain ⟨w_213, hw_213⟩ := h_w213_exists


              by_cases h_w123_eq_x : w_123 = x
              ·
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
                ·
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

                ·

                  have hx_not_U12 : x ∉ U_12 := by
                    intro hx_U12



                    unfold Survives at hw_123
                    simp only [List.foldl_cons, List.foldl_nil] at hw_123




                    have hx_best_U12 : ∀ y ∈ U_12, setup.score s3 y ≤ setup.score s3 x := by
                      intro y hy
                      have hy_I : y ∈ I := h_U12_subset_I hy
                      exact hx_best y hy_I


                    have h_top_card : (computeTopHalf setup s3 U_12).card = 1 := by
                      rw [computeTopHalf_card, h_U12_card]
                      norm_num


                    have hx_in_top : x ∈ computeTopHalf setup s3 U_12 := by

                      apply max_score_in_computeTopHalf setup s3 U_12 x 1
                      · exact hx_U12
                      · exact hx_best_U12
                      · omega
                      · rw [h_U12_card]; omega


                    have : computeTopHalf setup s3 U_12 = {x} := by
                      have : (computeTopHalf setup s3 U_12).card = 1 := h_top_card
                      exact Finset.card_eq_one.mp this |>.choose_spec |> fun h =>
                        Finset.eq_singleton_iff_unique_mem.mpr ⟨hx_in_top, fun y hy =>
                          if h_eq : y = x then h_eq else by

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

                    unfold Survives at hw_213
                    simp only [List.foldl_cons, List.foldl_nil] at hw_213


                    have hx_best_U21 : ∀ y ∈ U_21, setup.score s3 y ≤ setup.score s3 x := by
                      intro y hy
                      have hy_I : y ∈ I := h_U21_subset_I hy
                      exact hx_best y hy_I


                    have h_top_card : (computeTopHalf setup s3 U_21).card = 1 := by
                      rw [computeTopHalf_card, h_U21_card]
                      norm_num


                    have hx_in_top : x ∈ computeTopHalf setup s3 U_21 := by

                      apply max_score_in_computeTopHalf setup s3 U_21 x 1
                      · exact hx_U21
                      · exact hx_best_U21
                      · omega
                      · rw [h_U21_card]; omega


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


                  have h_U12_eq : U_12 = I \ {x} := by

                    have h_sub : U_12 ⊆ I \ {x} := by
                      intro y hy
                      rw [Finset.mem_sdiff]
                      constructor
                      · exact h_U12_subset_I hy
                      · rw [Finset.mem_singleton]
                        intro h_eq
                        rw [h_eq] at hy
                        exact hx_not_U12 hy

                    have h_diff_card : (I \ {x}).card = 2 := by
                      have hx_in_I : x ∈ I := hx_I
                      have : (I \ {x}).card = I.card - 1 := by
                        rw [Finset.card_sdiff]
                        · simp [Finset.card_singleton]
                        · exact Finset.singleton_subset_iff.mpr hx_in_I
                      rw [this, h_I_card]
                      omega

                    exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_U12_card, h_diff_card])


                  have h_U21_eq : U_21 = I \ {x} := by

                    have h_sub : U_21 ⊆ I \ {x} := by
                      intro y hy
                      rw [Finset.mem_sdiff]
                      constructor
                      · exact h_U21_subset_I hy
                      · rw [Finset.mem_singleton]
                        intro h_eq
                        rw [h_eq] at hy
                        exact hx_not_U21 hy

                    have h_diff_card : (I \ {x}).card = 2 := by
                      have hx_in_I : x ∈ I := hx_I
                      have : (I \ {x}).card = I.card - 1 := by
                        rw [Finset.card_sdiff]
                        · simp [Finset.card_singleton]
                        · exact Finset.singleton_subset_iff.mpr hx_in_I
                      rw [this, h_I_card]
                      omega

                    exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_U21_card, h_diff_card])


                  have h_U12_eq_U21_contra : U_12 = U_21 := by
                    rw [h_U12_eq, h_U21_eq]


                  exact h_U12_eq_U21 h_U12_eq_U21_contra

            ·






              have h_U23_card : U_23.card = 2 := computeTopHalf_card setup s3 S2


              have h_exists_y : ∃ y ∈ U_23, y ≠ x := by

                by_contra h_not
                push_neg at h_not

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





              have h_w231_eq_y : w_231 = y := by

                unfold Survives at hw_231
                simp only [List.foldl_cons, List.foldl_nil] at hw_231



                have h_top_card : (computeTopHalf setup s1 U_23).card = 1 := by
                  rw [computeTopHalf_card, h_U23_card]
                  norm_num


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


                have : w_231 = x ∨ w_231 = y := by

                  have h_U23_eq : U_23 = {x, y} := by
                    ext z
                    constructor
                    · intro hz
                      rw [Finset.mem_insert, Finset.mem_singleton]
                      by_cases h_eq_x : z = x
                      · left; exact h_eq_x
                      · right

                        by_cases h_eq_y : z = y
                        · exact h_eq_y
                        ·

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


















































                have hy_I : y ∈ I := by


                  rw [Finset.mem_inter]
                  constructor
                  ·

                    by_contra hy_not_S1



                    have hx_S1 : x ∈ S1 := Finset.mem_inter.mp hx_I |>.1
                    unfold S1 at hx_S1 hy_not_S1


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



                    have h_w231_eq_x_contra : w_231 = x := by

                      unfold Survives at hw_231
                      simp only [List.foldl_cons, List.foldl_nil] at hw_231




                      have h_U23_eq : U_23 = {x, y} := h_U23_eq


                      have hx_best_s1_U23 : ∀ z ∈ U_23, setup.score s1 z ≤ setup.score s1 x := by
                        intro z hz
                        rw [h_U23_eq] at hz
                        rw [Finset.mem_insert, Finset.mem_singleton] at hz
                        cases hz with
                        | inl h => rw [h]
                        | inr h => rw [h]; omega


                      have h_top_card : (computeTopHalf setup s1 U_23).card = 1 := by
                        rw [computeTopHalf_card, h_U23_card]
                        norm_num


                      have hx_in_top : x ∈ computeTopHalf setup s1 U_23 := by
                        have hx_in_U23 : x ∈ U_23 := by rw [h_U23_eq]; simp
                        apply max_score_in_computeTopHalf setup s1 U_23 x 1
                        · exact hx_in_U23
                        · exact hx_best_s1_U23
                        · omega
                        · rw [h_U23_card]; omega


                      have h_singleton : ∃ a, computeTopHalf setup s1 U_23 = {a} := Finset.card_eq_one.mp h_top_card
                      obtain ⟨a, ha⟩ := h_singleton
                      rw [ha] at hx_in_top hw_231
                      rw [Finset.mem_singleton] at hx_in_top hw_231
                      rw [← hx_in_top, hw_231]


                    exact h_w231_eq_x h_w231_eq_x_contra
                  · exact hy_S2




              by_cases hy_U12 : y ∈ U_12
              ·



                by_cases h_y_best_U12 : y ∈ computeTopHalf setup s3 U_12
                ·
                  have h_w123_exists : ∃ w, Survives setup [s1, s2, s3] w := survives_exists setup [s1, s2, s3] (by decide)
                  obtain ⟨w_123, hw_123⟩ := h_w123_exists


                  have hw_123_top : w_123 ∈ computeTopHalf setup s3 U_12 := by
                    unfold Survives at hw_123
                    simp only [List.foldl_cons, List.foldl_nil] at hw_123
                    exact hw_123


                  have h_top_card : (computeTopHalf setup s3 U_12).card = 1 := by
                    rw [computeTopHalf_card, h_U12_card]
                    norm_num

                  have : computeTopHalf setup s3 U_12 = {y} := by

                    have h_singleton : ∃ a, computeTopHalf setup s3 U_12 = {a} := Finset.card_eq_one.mp h_top_card
                    obtain ⟨a, ha⟩ := h_singleton

                    rw [ha] at h_y_best_U12
                    rw [Finset.mem_singleton] at h_y_best_U12
                    rw [← h_y_best_U12]
                    exact ha

                  rw [this] at hw_123_top
                  rw [Finset.mem_singleton] at hw_123_top
                  have h_w123_eq_y : w_123 = y := hw_123_top


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

                ·



                  have h_w123_exists : ∃ w, Survives setup [s1, s2, s3] w := survives_exists setup [s1, s2, s3] (by decide)
                  obtain ⟨w_123, hw_123⟩ := h_w123_exists


                  have hw_123_top : w_123 ∈ computeTopHalf setup s3 U_12 := by
                    unfold Survives at hw_123
                    simp only [List.foldl_cons, List.foldl_nil] at hw_123
                    exact hw_123


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


                  have hw_123_ne_y : w_123 ≠ y := by
                    intro h_eq
                    rw [h_eq] at hw_123_top
                    exact h_y_best_U12 hw_123_top



                  by_cases hw_123_eq_x : w_123 = x
                  ·

                    have h_w213_exists : ∃ w, Survives setup [s2, s1, s3] w := survives_exists setup [s2, s1, s3] (by decide)
                    obtain ⟨w_213, hw_213⟩ := h_w213_exists


                    have hw_213_top : w_213 ∈ computeTopHalf setup s3 U_21 := by
                      unfold Survives at hw_213
                      simp only [List.foldl_cons, List.foldl_nil] at hw_213
                      exact hw_213


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


                    by_cases hx_U21 : x ∈ U_21
                    ·
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

                    ·
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


                      have hy_U21 : y ∈ U_21 := by
                        rw [h_U21_eq]
                        rw [Finset.mem_sdiff]
                        constructor
                        · exact hy_I
                        · rw [Finset.mem_singleton]
                          exact hy_ne_x


                      by_cases hw_213_eq_y : w_213 = y
                      ·
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

                      ·









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


                        have hw_213_I : w_213 ∈ I := h_U21_subset_I hw_213_in_U21


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










                        have h_y_better_w213 : setup.score s3 y > setup.score s3 w_213 := by

                          by_cases hw_213_U23 : w_213 ∈ U_23
                          ·
                            have h_U23_eq : U_23 = {x, y} := h_U23_eq
                            rw [h_U23_eq] at hw_213_U23
                            rw [Finset.mem_insert, Finset.mem_singleton] at hw_213_U23
                            cases hw_213_U23 with
                            | inl h => exact absurd h hw_213_not_x
                            | inr h => exact absurd h hw_213_eq_y
                          ·

                            have hw_213_S2 : w_213 ∈ S2 := by
                              have : I ⊆ S2 := Finset.inter_subset_right
                              exact this hw_213_I
                            have hw_213_diff : w_213 ∈ S2 \ U_23 := by
                              rw [Finset.mem_sdiff]
                              exact ⟨hw_213_S2, hw_213_U23⟩

                            have hy_U23_mem : y ∈ U_23 := hy_U23

                            unfold U_23 at hy_U23_mem hw_213_diff

                            have : setup.score s3 y ≥ setup.score s3 w_213 := by
                              exact computeTopHalf_score_property setup s3 S2 y hy_U23_mem w_213 hw_213_diff
                            by_contra h_not_gt
                            push_neg at h_not_gt
                            have : setup.score s3 y = setup.score s3 w_213 := by omega
                            have h_inj := setup.score_injective s3
                            have : y = w_213 := h_inj this
                            exact hw_213_eq_y this.symm



                        have h_w213_better_y : setup.score s3 w_213 ≥ setup.score s3 y := by


                          have hy_U21_mem : y ∈ U_21 := hy_U21
                          by_cases hy_top : y ∈ computeTopHalf setup s3 U_21
                          ·

                            have h_top_card : (computeTopHalf setup s3 U_21).card = 1 := by
                              rw [computeTopHalf_card, h_U21_card]
                              norm_num

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
                          ·
                            have hy_diff : y ∈ U_21 \ computeTopHalf setup s3 U_21 := by
                              rw [Finset.mem_sdiff]
                              exact ⟨hy_U21_mem, hy_top⟩
                            exact computeTopHalf_score_property setup s3 U_21 w_213 hw_213_top y hy_diff


                        omega

                  ·




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


                    have h_score_y_ge_w123 : setup.score s3 y ≥ setup.score s3 w_123 :=
                      computeTopHalf_score_property setup s3 S2 y hy_U23 w_123 hw_123_diff
                    omega

              ·
                by_cases hy_U21 : y ∈ U_21
                ·

                  have h_w213_exists : ∃ w, Survives setup [s2, s1, s3] w := survives_exists setup [s2, s1, s3] (by decide)
                  obtain ⟨w_213, hw_213⟩ := h_w213_exists
                  have hw_213_top : w_213 ∈ computeTopHalf setup s3 U_21 := by
                    unfold Survives at hw_213
                    simp only [List.foldl_cons, List.foldl_nil] at hw_213
                    exact hw_213


                  by_cases hy_top : y ∈ computeTopHalf setup s3 U_21
                  ·
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
                  ·
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
                    ·
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
                ·








                  have h_U12_sub : U_12 ⊆ I \ {y} := by
                    intro z hz
                    rw [Finset.mem_sdiff]
                    constructor
                    · exact h_U12_subset_I hz
                    · rw [Finset.mem_singleton]
                      intro h_eq
                      rw [h_eq] at hz
                      exact hy_U12 hz


                  have h_U21_sub : U_21 ⊆ I \ {y} := by
                    intro z hz
                    rw [Finset.mem_sdiff]
                    constructor
                    · exact h_U21_subset_I hz
                    · rw [Finset.mem_singleton]
                      intro h_eq
                      rw [h_eq] at hz
                      exact hy_U21 hz


                  have h_diff_card : (I \ {y}).card = 2 := by
                    have hy_in_I : y ∈ I := hy_I
                    have : (I \ {y}).card = I.card - 1 := by
                      rw [Finset.card_sdiff]
                      · simp [Finset.card_singleton]
                      · exact Finset.singleton_subset_iff.mpr hy_in_I
                    rw [this, h_I_card]
                    omega


                  have h_U12_eq_diff : U_12 = I \ {y} := Finset.eq_of_subset_of_card_le h_U12_sub (by rw [h_U12_card, h_diff_card])
                  have h_U21_eq_diff : U_21 = I \ {y} := Finset.eq_of_subset_of_card_le h_U21_sub (by rw [h_U21_card, h_diff_card])


                  have h_U12_eq_U21_contra : U_12 = U_21 := by
                    rw [h_U12_eq_diff, h_U21_eq_diff]


                  exact h_U12_eq_U21 h_U12_eq_U21_contra


        exact h_count_le_5
      ·
        have h12_eq_4 : (S1 ∩ S2).card = 4 := by
          have : (S1 ∩ S2).card ≤ min S1.card S2.card := inter_card_le_min S1 S2
          rw [h_S1_card, h_S2_card] at this
          simp at this
          omega

        have h_S1_eq_S2 : S1 = S2 := eq_of_inter_card_eq_four S1 S2 h_S1_card h_S2_card h12_eq_4




        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          have h_le_6 := champions_le_six setup
          by_contra h_not_le_5
          push_neg at h_not_le_5
          have h_eq_6 : countPotentialChampions setup = 6 := by omega






          let U_12 := computeTopHalf setup s2 S1
          let U_21 := computeTopHalf setup s1 S2
          let U_13 := computeTopHalf setup s3 S1
          let U_23 := computeTopHalf setup s3 S2


          have h_U13_eq_U23 : U_13 = U_23 := by
            unfold U_13 U_23
            rw [h_S1_eq_S2]

          let Y := U_13


























          have h_Y_card : Y.card = 2 := by
            unfold Y U_13
            exact computeTopHalf_card setup s3 S1

          have h_U12_card : U_12.card = 2 := computeTopHalf_card setup s2 S1
          have h_U21_card : U_21.card = 2 := by
            rw [← h_S1_eq_S2]
            exact computeTopHalf_card setup s1 S2


          by_cases h_U12_inter : (U_12 ∩ Y).Nonempty
          ·





            have h_Y_top_scores : ∀ y ∈ Y, ∀ x ∈ S1 \ Y, setup.score s3 y ≥ setup.score s3 x := by
              unfold Y U_13
              exact computeTopHalf_score_property setup s3 S1


            have h_U12_subset : U_12 ⊆ S1 := computeTopHalf_subset setup s2 S1





            have h_inter_better : ∀ u ∈ U_12 ∩ Y, ∀ v ∈ U_12 \ Y, setup.score s3 u ≥ setup.score s3 v := by
              intro u hu v hv
              have hu_Y : u ∈ Y := Finset.mem_inter.mp hu |>.2
              have hv_U12 : v ∈ U_12 := Finset.mem_sdiff.mp hv |>.1
              have hv_not_Y : v ∉ Y := Finset.mem_sdiff.mp hv |>.2
              have hv_S1 : v ∈ S1 := h_U12_subset hv_U12
              have hv_S1_diff_Y : v ∈ S1 \ Y := Finset.mem_sdiff.mpr ⟨hv_S1, hv_not_Y⟩
              exact h_Y_top_scores u hu_Y v hv_S1_diff_Y






            have h_winner_in_inter : computeTopHalf setup s3 U_12 ⊆ U_12 ∩ Y := by
              intro w hw



              have hw_U12 : w ∈ U_12 := computeTopHalf_subset setup s3 U_12 hw


              by_contra hw_not_Y

              have hw_diff : w ∈ U_12 \ Y := Finset.mem_sdiff.mpr ⟨hw_U12, hw_not_Y⟩


              obtain ⟨u, hu_inter⟩ := h_U12_inter


              have h_score_u_ge_w : setup.score s3 u ≥ setup.score s3 w :=
                h_inter_better u hu_inter w hw_diff


              have hu_U12 : u ∈ U_12 := Finset.mem_inter.mp hu_inter |>.1











              by_cases hu_in_top : u ∈ computeTopHalf setup s3 U_12
              ·

                have h_card_1 : (computeTopHalf setup s3 U_12).card = 1 := by
                  rw [computeTopHalf_card, h_U12_card]
                  norm_num

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
              ·

                have hu_diff_top : u ∈ U_12 \ computeTopHalf setup s3 U_12 :=
                  Finset.mem_sdiff.mpr ⟨hu_U12, hu_in_top⟩

                have h_score_w_ge_u : setup.score s3 w ≥ setup.score s3 u :=
                  computeTopHalf_score_property setup s3 U_12 w hw u hu_diff_top

                have h_eq : setup.score s3 u = setup.score s3 w := by omega





                have hu_w_eq : u = w := by







                  have h_inj := setup.score_injective s3
                  exact h_inj h_eq

                rw [← hu_w_eq] at hw_not_Y
                have hu_Y : u ∈ Y := Finset.mem_inter.mp hu_inter |>.2
                exact hw_not_Y hu_Y

            have h_winner_in_Y : computeTopHalf setup s3 U_12 ⊆ Y := by
              exact Finset.Subset.trans h_winner_in_inter Finset.inter_subset_right
























            have h_contradiction : countPotentialChampions setup ≤ 5 := by





              let ord1 := [s1, s2, s3]
              let ord2 := [s1, s3, s2]
              let ord3 := [s2, s3, s1]


              have h_winner1 : ∃ w ∈ Y, Survives setup ord1 w := by

                have h_surv : ∃ w, Survives setup ord1 w := survives_exists setup ord1 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                ·
                  unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw




                  have : w ∈ computeTopHalf setup s3 U_12 := hw
                  exact h_winner_in_Y this
                · exact hw

              have h_winner2 : ∃ w ∈ Y, Survives setup ord2 w := by

                have h_surv : ∃ w, Survives setup ord2 w := survives_exists setup ord2 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                ·
                  unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw




                  exact computeTopHalf_subset setup s2 Y hw
                · exact hw

              have h_winner3 : ∃ w ∈ Y, Survives setup ord3 w := by

                have h_surv : ∃ w, Survives setup ord3 w := survives_exists setup ord3 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                ·
                  unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw




                  exact computeTopHalf_subset setup s1 Y hw
                · exact hw


              obtain ⟨w1, hw1_Y, hw1_surv⟩ := h_winner1
              obtain ⟨w2, hw2_Y, hw2_surv⟩ := h_winner2
              obtain ⟨w3, hw3_Y, hw3_surv⟩ := h_winner3


              by_cases h12 : w1 = w2
              ·
                rw [← h12] at hw2_surv
                apply duplicate_winner_implies_count_le_five setup ord1 ord2
                ·
                  intro h_eq
                  simp only [ord1, ord2] at h_eq
                  injection h_eq with _ h_rest
                  injection h_rest
                ·
                  decide
                ·
                  decide
                · exact hw1_surv
                · exact hw2_surv
              · by_cases h13 : w1 = w3
                ·
                  rw [← h13] at hw3_surv
                  apply duplicate_winner_implies_count_le_five setup ord1 ord3
                  ·
                    intro h_eq
                    simp only [ord1, ord3] at h_eq
                    injection h_eq
                  · decide
                  · decide
                  · exact hw1_surv
                  · exact hw3_surv
                ·
                  have h23 : w2 = w3 := by


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
                  ·
                    intro h_eq
                    simp only [ord2, ord3] at h_eq
                    injection h_eq
                  · decide
                  · decide
                  · exact hw2_surv
                  · exact hw3_surv

            omega
          ·
            push_neg at h_U12_inter
            have h_U12_disjoint : Disjoint U_12 Y := by
              rw [Finset.disjoint_iff_inter_eq_empty]
              exact Finset.not_nonempty_iff_eq_empty.mp h_U12_inter




            have h_U12_subset : U_12 ⊆ S1 := computeTopHalf_subset setup s2 S1
            have h_Y_subset : Y ⊆ S1 := by
              unfold Y U_13
              exact computeTopHalf_subset setup s3 S1

            have h_U12_eq_diff : U_12 = S1 \ Y := by

              have h_sub : U_12 ⊆ S1 \ Y := by
                intro x hx
                rw [Finset.mem_sdiff]
                constructor
                · exact h_U12_subset hx
                · intro hx_Y
                  have : x ∈ U_12 ∩ Y := Finset.mem_inter.mpr ⟨hx, hx_Y⟩
                  exact Finset.disjoint_iff_inter_eq_empty.mp h_U12_disjoint ▸
                    Finset.not_mem_empty x this

              have h_diff_card : (S1 \ Y).card = S1.card - Y.card :=
                Finset.card_sdiff h_Y_subset
              rw [h_S1_card, h_Y_card] at h_diff_card

              exact Finset.eq_of_subset_of_card_le h_sub (by omega)


            by_cases h_U21_inter : (U_21 ∩ Y).Nonempty
            ·




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

                  have hu_w_eq : u = w := by
                    have h_inj := setup.score_injective s3
                    exact h_inj h_eq
                  rw [← hu_w_eq] at hw_not_Y
                  have hu_Y : u ∈ Y := Finset.mem_inter.mp hu_inter |>.2
                  exact hw_not_Y hu_Y


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

              omega
            ·
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


              have h_U12_eq_U21 : U_12 = U_21 := by
                rw [h_U12_eq_diff, h_U21_eq_diff]





              have h_S3_eq : computeTopHalf setup s3 U_12 = computeTopHalf setup s3 U_21 := by
                rw [h_U12_eq_U21]




              have h_exists_winner : ∃ (winner : Student),
                  Survives setup [s1, s2, s3] winner ∧ Survives setup [s2, s1, s3] winner := by


                have h_S3_nonempty : (computeTopHalf setup s3 U_12).Nonempty := by

                  have h_card : (computeTopHalf setup s3 U_12).card = U_12.card / 2 :=
                    computeTopHalf_card setup s3 U_12
                  rw [h_U12_card] at h_card
                  have : (computeTopHalf setup s3 U_12).card = 1 := by omega
                  exact Finset.card_pos.mp (by omega : 0 < (computeTopHalf setup s3 U_12).card)

                obtain ⟨winner, h_winner_mem⟩ := h_S3_nonempty

                use winner
                constructor
                ·
                  unfold Survives
                  simp only []
                  exact h_winner_mem
                ·
                  unfold Survives
                  simp only []
                  rw [← h_S3_eq]
                  exact h_winner_mem

              obtain ⟨winner, hw1, hw2⟩ := h_exists_winner


              have h_count_le_5' : countPotentialChampions setup ≤ 5 := by
                apply duplicate_winner_implies_count_le_five setup [s1, s2, s3] [s2, s1, s3]
                ·
                  intro h_eq
                  injection h_eq with h1 h2
                  exact hs12 h1
                ·
                  have : (univ : Finset Subject).toList ~ ({s1, s2, s3} : Finset Subject).toList := by
                    apply List.Perm.of_eq
                    congr 1
                    exact huniv
                  apply List.Perm.trans _ this
                  have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s1, s2, s3} := rfl
                  rw [← h_finset_eq]

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
                ·
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

              omega
        exact h_count_le_5
  · intro h_rest
    cases h_rest with
    | inl h23 =>





      by_cases h23_eq_2 : (S2 ∩ S3).card = 2
      ·







        have h_exists_winner : ∃ (winner : Student),
            Survives setup [s2, s3, s1] winner ∧ Survives setup [s3, s2, s1] winner := by


          apply size_two_intersection_property setup s2 s3 s1 hs23 hs13.symm hs12.symm

          exact h23_eq_2

        obtain ⟨winner, hw1, hw2⟩ := h_exists_winner

        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by

          apply duplicate_winner_implies_count_le_five setup [s2, s3, s1] [s3, s2, s1]
          ·
            intro h_eq
            injection h_eq with h1 h2
            exact hs23 h1.symm
          ·
            have : (univ : Finset Subject).toList ~ ({s1, s2, s3} : Finset Subject).toList := by
              apply List.Perm.of_eq
              congr 1
              exact huniv
            apply List.Perm.trans _ this

            have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s2, s3, s1} := by
              ext x
              simp
              tauto
            rw [← h_finset_eq]

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
          ·
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

      ·

        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          have h_le_6 := champions_le_six setup
          by_contra h_not_le_5
          push_neg at h_not_le_5
          have h_eq_6 : countPotentialChampions setup = 6 := by omega







          by_cases h23_eq_3 : (S2 ∩ S3).card = 3
          ·




            let I := S2 ∩ S3
            have h_I_card : I.card = 3 := h23_eq_3


            let U_23 := computeTopHalf setup s3 S2
            let U_32 := computeTopHalf setup s2 S3
            let U_31 := computeTopHalf setup s1 S3


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





            have h_U23_card : U_23.card = 2 := by
              unfold U_23
              exact computeTopHalf_card setup s3 S2
            have h_U32_card : U_32.card = 2 := by
              unfold U_32
              exact computeTopHalf_card setup s2 S3


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

            ·
              have h_I_nonempty : I.Nonempty := by
                rw [Finset.card_pos]
                rw [h_I_card]
                omega


              have h_exists_best : ∃ x ∈ I, ∀ z ∈ I, setup.score s1 z ≤ setup.score s1 x := by
                exact Finset.exists_max_image I (setup.score s1) h_I_nonempty
              obtain ⟨x, hx_I, hx_best⟩ := h_exists_best


              have h_I_subset_S3 : I ⊆ S3 := Finset.inter_subset_right
              have hx_in_U31 : x ∈ U_31 := by
                have hx_in_S3 : x ∈ S3 := h_I_subset_S3 hx_I
                apply at_most_k_minus_1_better_implies_in_top_k setup s1 S3 x 2
                · exact hx_in_S3
                · omega
                · rw [h_S3_card]; omega
                ·
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


              have h_w312_exists : ∃ w, Survives setup [s3, s1, s2] w :=
                survives_exists setup [s3, s1, s2] (by decide)
              obtain ⟨w_312, hw_312⟩ := h_w312_exists

              by_cases h_w312_eq_x : w_312 = x
              ·
                by_cases hx_U23 : x ∈ U_23
                ·
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
                ·
                  by_cases hx_U32 : x ∈ U_32
                  ·
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
                  ·
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

              ·






                have h_w231_exists : ∃ w, Survives setup [s2, s3, s1] w :=
                  survives_exists setup [s2, s3, s1] (by decide)
                obtain ⟨w_231, hw_231⟩ := h_w231_exists
                have h_w321_exists : ∃ w, Survives setup [s3, s2, s1] w :=
                  survives_exists setup [s3, s2, s1] (by decide)
                obtain ⟨w_321, hw_321⟩ := h_w321_exists

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
                ·

                  have h_three : ({w_231, w_321, w_312} : Finset Student).card ≥ 3 := by
                    by_contra h_not
                    push_neg at h_not

                    have h_dup : w_231 = w_321 ∨ w_231 = w_312 ∨ w_321 = w_312 := by

                      have : ({w_231, w_321, w_312} : Finset Student).card ≤ 2 := by omega

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

          ·
            have h23_eq_4 : (S2 ∩ S3).card = 4 := by
              have : (S2 ∩ S3).card ≤ min S2.card S3.card := inter_card_le_min S2 S3
              rw [h_S2_card, h_S3_card] at this
              simp at this
              omega

            have h_S2_eq_S3 : S2 = S3 := eq_of_inter_card_eq_four S2 S3 h_S2_card h_S3_card h23_eq_4

            have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
              have h_le_6 := champions_le_six setup
              by_contra h_not_le_5
              push_neg at h_not_le_5
              have h_eq_6 : countPotentialChampions setup = 6 := by omega


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

                  exact computeTopHalf_subset setup s3 Y hw
                · exact hw

              have h_winner2 : ∃ w ∈ Y, Survives setup ord2 w := by
                have h_surv : ∃ w, Survives setup ord2 w := survives_exists setup ord2 (by decide)
                obtain ⟨w, hw⟩ := h_surv
                use w
                constructor
                · unfold Survives at hw
                  simp only [List.foldl_cons, List.foldl_nil] at hw

                  exact computeTopHalf_subset setup s2 Y hw
                · exact hw


              by_cases h_U23_inter : (U_23 ∩ Y).Nonempty
              · have h_winner3 : ∃ w ∈ Y, Survives setup ord3 w := by
                  have h_surv : ∃ w, Survives setup ord3 w := survives_exists setup ord3 (by decide)
                  obtain ⟨w, hw⟩ := h_surv
                  use w
                  constructor
                  · unfold Survives at hw
                    simp only [List.foldl_cons, List.foldl_nil] at hw


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

              ·
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


                      by_contra h_ne
                      have h_nonempty : (U_32 ∩ Y).Nonempty := by
                        rw [Finset.nonempty_iff_ne_empty]
                        exact h_ne

                      exact (h_U23_inter (by


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


                have h_U23_eq_U32 : U_23 = U_32 := by
                  rw [h_U23_eq, h_U32_eq, h_S2_eq_S3]


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





      by_cases h31_eq_2 : (S3 ∩ S1).card = 2
      ·



        have h_exists_winner : ∃ (winner : Student),
            Survives setup [s3, s1, s2] winner ∧ Survives setup [s1, s3, s2] winner := by


          apply size_two_intersection_property setup s3 s1 s2 hs13 hs12 hs23

          exact h31_eq_2

        obtain ⟨winner, hw1, hw2⟩ := h_exists_winner

        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by

          apply duplicate_winner_implies_count_le_five setup [s3, s1, s2] [s1, s3, s2]
          ·
            intro h_eq
            injection h_eq with h1 h2
            exact hs13 h1
          ·
            have : (univ : Finset Subject).toList ~ ({s1, s2, s3} : Finset Subject).toList := by
              apply List.Perm.of_eq
              congr 1
              exact huniv
            apply List.Perm.trans _ this

            have h_finset_eq : ({s1, s2, s3} : Finset Subject) = {s3, s1, s2} := by
              ext x
              simp
              tauto
            rw [← h_finset_eq]

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
          ·
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

      ·

        have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
          have h_le_6 := champions_le_six setup
          by_contra h_not_le_5
          push_neg at h_not_le_5
          have h_eq_6 : countPotentialChampions setup = 6 := by omega







          by_cases h31_eq_3 : (S3 ∩ S1).card = 3
          ·




            let I := S3 ∩ S1
            have h_I_card : I.card = 3 := h31_eq_3


            let U_31 := computeTopHalf setup s1 S3
            let U_13 := computeTopHalf setup s3 S1
            let U_12 := computeTopHalf setup s2 S1


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



            have h_U31_card : U_31.card = 2 := by
              unfold U_31
              exact computeTopHalf_card setup s1 S3
            have h_U13_card : U_13.card = 2 := by
              unfold U_13
              exact computeTopHalf_card setup s3 S1


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

            ·
              have h_I_nonempty : I.Nonempty := by
                rw [Finset.card_pos]
                rw [h_I_card]
                omega

              have h_exists_best : ∃ x ∈ I, ∀ z ∈ I, setup.score s2 z ≤ setup.score s2 x := by
                exact Finset.exists_max_image I (setup.score s2) h_I_nonempty
              obtain ⟨x, hx_I, hx_best⟩ := h_exists_best


              have h_I_subset_S1 : I ⊆ S1 := Finset.inter_subset_right
              have hx_in_U12 : x ∈ U_12 := by
                have hx_in_S1 : x ∈ S1 := h_I_subset_S1 hx_I
                apply at_most_k_minus_1_better_implies_in_top_k setup s2 S1 x 2
                · exact hx_in_S1
                · omega
                · rw [h_S1_card]; omega
                ·
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


              have h_w123_exists : ∃ w, Survives setup [s1, s2, s3] w :=
                survives_exists setup [s1, s2, s3] (by decide)
              obtain ⟨w_123, hw_123⟩ := h_w123_exists

              by_cases h_w123_eq_x : w_123 = x
              ·
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
                  ·
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

              ·
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
                ·
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

          ·
            have h31_eq_4 : (S3 ∩ S1).card = 4 := by
              have : (S3 ∩ S1).card ≤ min S3.card S1.card := inter_card_le_min S3 S1
              rw [h_S3_card, h_S1_card] at this
              simp at this
              omega

            have h_S3_eq_S1 : S3 = S1 := eq_of_inter_card_eq_four S3 S1 h_S3_card h_S1_card h31_eq_4

            have h_count_le_5 : countPotentialChampions setup ≤ 5 := by
              have h_le_6 := champions_le_six setup
              by_contra h_not_le_5
              push_neg at h_not_le_5
              have h_eq_6 : countPotentialChampions setup = 6 := by omega


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

              ·
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
  ·
    intros Student Subject _ _ _ _ setup
    exact champions_le_five setup
  ·
    use (Fin 8), (Fin 3), inferInstance, inferInstance, inferInstance, inferInstance
    use exampleSetup
    exact example_count

/-- 题目 1.1 的最终陈述（与 problem_statement 等价） -/
theorem prob1_1 : ∃ n, IsMaxPotentialChampions n := by
  exact problem_statement

end
end CompetitionSetup
