# Can a Simple Automated AI Pipeline Solve Research-Level Mathematical Problems?

> 一个 **自动化 AI 数学推理** 的开源项目 —— 评估下一代大语言模型在 **研究级数学问题** 上的真实能力，包含 ICCM 官方挑战题、First Proof 未发表研究题、完整 AI 解答及 Lean 4 形式化验证尝试。

[![arXiv](https://img.shields.io/badge/arXiv-2602.05192-b31b1b)](https://arxiv.org/abs/2602.05192)
[![GitHub](https://img.shields.io/badge/GitHub-ml1301215-blue?logo=github)](https://github.com/ml1301215)
[![License: CC BY-NC 4.0](https://img.shields.io/badge/License-CC%20BY--NC%204.0-lightgrey)](LICENSE)
[![Status](https://img.shields.io/badge/status-active-success)]()
[![Paper](https://img.shields.io/badge/PDF-Download-red)](Can%20a%20Simple%20Automated%20AI%20Pipeline%20Solve%20Research-Level%20Mathematical%20Problems.pdf)

---

## 📖 项目简介

**大型语言模型真的能推动数学研究吗？**  
2026 年，我们正站在一个转折点上。本研究证明：**通过轻量级、纯自然语言的自动化流水线，并引入“引文增强验证”机制**，下一代 LLM（Gemini 3 Pro、GPT‑5.2 Pro）**能够可靠地解决研究级数学问题**，而不仅仅是竞赛题。

我们构建的流水线在 **ICCM 官方挑战题**（丘成桐大学生数学竞赛难度）上达到 **100% 解决率**；在 **10 道从未发表的 First Proof 研究题** 上全部生成候选证明，其中 **Problem 4 已通过数学博士团队的严格人工验证**，确认为正确证明。

本项目完全开源以下内容：
- 📄 **论文全文**（含完整方法论、实验设计、结果分析）
- 📚 **全部题目原文**（ICCM 三组题 + First Proof 十道题）
- ✅ **AI 生成的自然语言解答**（ICCM 第 1、2 组完整证明；First Proof 全部候选证明）
- 🧠 **Lean 4 形式化验证尝试**（ICCM 组合题）
- 🧪 **即将开放**：自动化流水线代码、提示模板、引文验证模块

---

## 📄 论文与引用

**论文标题**：*Can a Simple Automated AI Pipeline Solve Research-Level Mathematical Problems?*  
**作者**：AI Mathematics Research Team  
**预印本**：[arXiv:2602.05192](https://arxiv.org/abs/2602.05192)  
**最新版本**：`v1` (2026‑02‑12)

```bibtex
@misc{ai4math2026,
  title={Can a Simple Automated AI Pipeline Solve Research-Level Mathematical Problems?},
  author={AI Mathematics Research Team},
  year={2026},
  eprint={2602.05192},
  archivePrefix={arXiv},
  primaryClass={cs.AI}
}
```

---

## 🧩 项目结构

```
.
├── README.md
├── LICENSE
├── Can a Simple Automated AI Pipeline Solve Research-Level Mathematical Problems.pdf   # 论文全文
├── Prob1_1.lean                                        # Lean 4 形式化（潜在冠军题）
│
├── Problem_sets/                                       # 原始题目
│   ├── ICCM_problem_sets/                             # ICCM 官方挑战题
│   │   ├── test_1/                                    # 第1组 6 题
│   │   ├── test_2/                                    # 第2组 6 题
│   │   └── test_3/                                    # 第3组 6 题
│   └── First_Proof_problem_set/                       # First Proof 10 道研究题
│
├── Solutions_by_ai/                                   # AI 生成的自然语言解答
│   ├── ICCM/                                          # ICCM 第1、2组 PDF 解答
│   │   ├── 1/                                         # 1_1.pdf ~ 1_6.pdf
│   │   └── 2/                                         # 2_1.pdf ~ 2_6.pdf
│   └── First_Proof/                                   # First Proof 10 题候选解答
│       └── 1.pdf ~ 10.pdf

```

---

## 📊 数据集与结果总览

| 数据集                  | 问题数量 | AI 声称解决 | 人工验证进度                         | 最终状态               |
|------------------------|--------|------------|--------------------------------------|----------------------|
| **ICCM Set 1**         | 6      | 6 (100%)   | 全部复核通过（项目组数学成员）       | ✅ 已提交 ICCM 官方    |
| **ICCM Set 2**         | 6      | 6 (100%)   | 全部复核通过                         | ✅ 已提交 ICCM 官方    |
| **ICCM Set 3**         | 12+    | 部分尝试   | 猜想部分：AI 承认失败；<br>CY 问题：未验证 | ⏳ 待领域专家审阅   |
| **First Proof**        | 10     | 10 (100%)  | **Problem 4** 已严格验证（数学博士团队）<br>其余9题待验证 | 🟡 验证瓶颈           |


## 🔬 Lean 4 形式化探索

除自然语言证明外，我们对 ICCM 第1组中一道高难度组合题（潜在冠军题）尝试了 **Lean 4 形式化验证**。  
文件位置：`Prob1_1.lean`（根目录）  
目前已完成部分核心引理的形式化，**完整形式化证明仍在进行中**，欢迎社区贡献。

---


## 📜 许可证

本项目的**论文、题目文本、AI 生成解答**采用 **CC BY-NC 4.0 许可证**。  
**代码部分**采用 **MIT 许可证**，敬请留意各子目录下的单独声明。

---

## 📬 联系方式

- GitHub Issues：[https://github.com/ml1301215/.../issues](https://github.com/ml1301215/...)  
- 论文通讯作者（项目维护者）：可通过 GitHub 直接 @ml1301215

---

## 🌟 致谢

感谢 ICCM 组委会发布公开挑战题，感谢 Mohammed Abouzaid 等数学家提供 First Proof 问题集并参与验证。  
本工作受益于北京中关村人工智能研究院多位师生的讨论，在此一并致谢。

---

**如果本项目对您的研究有所启发，欢迎引用我们的论文，或给一颗 ⭐ 支持！**
```
