# 数学证明与竞赛习题集

> 一个结合 AI 自动化求解与形式化证明的数学问题集项目
[![GitHub](https://img.shields.io/badge/GitHub-ml1301215-blue?logo=github)](https://github.com/ml1301215)

## 项目简介

本项目是论文 **《Can a Simple Automated AI Pipeline Solve Research-Level
Mathematical Problems》** 的开源内容，收集了ICCM提出的习题https://mp.weixin.qq.com/s/，并提供了完整的 **AI 解答** 。同时我们还对ICCM中的一道组合题进行了**Lean 4 形式化证明** 的尝试。

📄 **论文**：见根目录 [Can a Simple Automated AI Pipeline Solve Research-Level Mathematical Problems.pdf](Can%20a%20Simple%20Automated%20AI%20Pipeline%20Solve%20Research-Level%20Mathematical%20Problems.pdf)

## 项目结构

```
.
├── Can a Simple Automated AI Pipeline Solve Research-Level
Mathematical Problems.pdf           # 论文
├── Prob1_1.lean              # Lean 4 形式化证明（潜在冠军问题）
├── Problem_sets/             # 习题题目
│   ├── ICCM_problem_sets/    
│   └── First_Proof_problem_set/ 
└── Solutions_by_ai/          # AI 解答
    ├── First_Proof/          
    └── ICCM/                 
```


## 许可证

本项目仅供学习与交流使用。

## 贡献

欢迎提交 Issue 与 Pull Request，包括：

- 新习题的解答与形式化
- 对现有证明的改进与补充
- 对题目或解答的勘误
