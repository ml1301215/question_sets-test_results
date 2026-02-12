# 数学证明与竞赛习题集

> 一个结合 AI 辅助求解与形式化证明的数学问题集项目 —— 本仓库为对应论文的开源部分

[![GitHub](https://img.shields.io/badge/GitHub-ml1301215-blue?logo=github)](https://github.com/ml1301215)

## 项目简介

本项目是论文 **《阶段性paper》** 的开源配套内容，收集了多套数学竞赛与习题集的题目，并提供了 **AI 辅助求解** 与 **Lean 4 形式化证明** 的尝试。通过人机协作的方式，探索将数学问题从自然语言理解、手工推理到机器可验证证明的完整流程。

📄 **论文**：见根目录 [阶段性paper.pdf](阶段性paper.pdf)

## 项目结构

```
.
├── 阶段性paper.pdf           # 对应论文
├── Prob1_1.lean              # Lean 4 形式化证明（潜在冠军问题）
├── Problem_sets/             # 习题题目
│   ├── ICCM_problem_sets/    # ICCM 问题题
│   ├── First_Proof_problem_set/  # 初次证明习题集
│   └── Exercises_from_Kasiwara/  # Kashiwara 范畴论习题
└── Solutions_by_ai/          # AI 辅助解答
    ├── First_Proof/          # 初次证明习题解答（PDF）
    └── ICCM/                 # ICCM 习题解答（PDF + Python 代码）
```

## 习题来源

| 习题集 | 领域 | 说明 |
|-------|------|------|
| **ICCM Problem Sets** | 组合/竞赛数学 | 如 8 学生 3 科目的「潜在冠军」问题 |
| **First Proof Problem Set** | 分析与概率 | 如 Φ⁴₃ 测度、分布理论 |
| **Exercises from Kashiwara** | 范畴论 | Yoneda 扩张、左正合函子等 |

## 技术栈

- **Lean 4** + **Mathlib**：形式化证明
- **Python**：穷举验证、构造与模拟（如潜在冠军淘汰赛）
- **AI 工具**：DeepSeek、Tree 等辅助推理与编程

## 典型示例：潜在冠军问题

**题目**：8 名学生、3 门科目，每科中每位学生的排名不同。若按 6 种科目顺序依次淘汰（每次淘汰一半），在至少一种顺序下能留到最后的学生称为「潜在冠军」。求潜在冠军的最大可能人数并证明。

**解答方式**：

1. **AI 推理**：用 DeepSeek 理解题意、抽象为矩阵问题并给出构造
2. **穷举验证**：用 Python 枚举大量矩阵，验证上界为 5
3. **形式化证明**：在 Lean 4 中形式化并验证结论（`Prob1_1.lean`）

详见 `Solutions_by_ai/ICCM/1/1_1/` 下的解答说明与代码。

## 环境要求

### Lean 4

- [Lean 4](https://lean-lang.org/lean4/)
- [Mathlib](https://github.com/leanprover-community/mathlib4)

### Python（用于 ICCM 解答中的脚本）

- Python 3.x
- 标准库即可，无需额外依赖

## 使用方式

### 查看 Lean 证明

```bash
lake build
```

### 运行 Python 验证脚本

```bash
cd Solutions_by_ai/ICCM/1/1_1/1_1解答code/
python solution.py
```

## 许可证

本项目仅供学习与交流使用。各习题集版权归原作者所有，请勿用于商业目的。

## 贡献

欢迎提交 Issue 与 Pull Request，包括：

- 新习题的解答与形式化
- 对现有证明的改进与补充
- 对题目或解答的勘误

## 作者

[ml1301215](https://github.com/ml1301215)
