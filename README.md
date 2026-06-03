# MARD

Problem sets and AI-generated solutions from [arXiv:2602.13695](https://arxiv.org/abs/2602.13695) — *Can a Lightweight Automated AI Pipeline Solve Research-Level Mathematical Problems?*

## Repository Structure

```
Problem_sets/
├── ICCM_problem_sets/
│   ├── test_1/   # ICCM round 1 — 6 problems (plain text)
│   ├── test_2/   # ICCM round 2 — 6 problems (plain text)
│   └── test_3/   # ICCM 2025   — 6 problems (plain text)
└── First_Proof_problem_set/
    ├── 10_problems_statements.pdf   # 10 research-level problems (PDF)
    └── test_5_*.txt                 # Same problems in plain text format

Solutions_by_ai/
├── ICCM/
│   ├── 1/   # AI solutions to ICCM round 1 (6 PDFs)
│   └── 2/   # AI solutions to ICCM round 2 (6 PDFs)
└── First_Proof/
    └── *.pdf   # AI candidate proofs for all 10 First Proof problems
```

For Lean 4 formalized proofs, see the companion repository: [lean4-math-formalization](https://github.com/ml1301215/lean4-math-formalization)

## Problem Sources

**ICCM** (International Congress of Chinese Mathematicians) annual competition problems, difficulty comparable to the S.-T. Yau College Student Mathematics Contest.

**First Proof** — unpublished research-level problems contributed by mathematicians. None had published solutions at the time of the study. Problem 4 has been verified as a correct proof by a mathematics PhD team.

## Data Format

| Folder | Format | Description |
|--------|--------|-------------|
| `Problem_sets/ICCM_problem_sets/` | `.txt` | Problem statements, one file per problem |
| `Problem_sets/First_Proof_problem_set/` | `.pdf`, `.txt` | 10 research-level problem statements |
| `Solutions_by_ai/ICCM/` | `.pdf` | AI-generated solutions to ICCM problems |
| `Solutions_by_ai/First_Proof/` | `.pdf` | AI candidate proofs for First Proof problems |

## Paper

```bibtex
@misc{meng2026lightweight,
  title         = {Can a Lightweight Automated AI Pipeline Solve Research-Level Mathematical Problems?},
  author        = {Lve Meng and Weilong Zhao and Yanzhi Zhang and Haoxiang Guan and Jiyan He},
  year          = {2026},
  eprint        = {2602.13695},
  archivePrefix = {arXiv}
}
```

## Contact

Lve Meng — [ml130@mail.ustc.edu.cn](mailto:ml130@mail.ustc.edu.cn)

## License

CC BY-NC 4.0
