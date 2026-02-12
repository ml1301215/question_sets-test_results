# 将项目上传到 GitHub 指南

## 当前进度

- [x] 已创建 `.gitignore`
- [x] 已初始化 Git 仓库
- [x] 已添加所有文件到暂存区
- [ ] 需要配置 Git 用户信息
- [ ] 需要完成首次提交
- [ ] 需要在 GitHub 创建仓库并推送

---

## 第一步：配置 Git 用户信息（如未配置过）

在终端执行（将邮箱和用户名替换为你自己的）：

```bash
git config --global user.email "你的邮箱@example.com"
git config --global user.name "ml1301215"
```

> 若使用 GitHub 隐私邮箱：`ml1301215@users.noreply.github.com`

---

## 第二步：完成首次提交

在项目目录下执行：

```bash
git commit -m "Initial commit: 数学证明与竞赛习题集项目"
```

---

## 第三步：在 GitHub 创建新仓库

1. 打开 https://github.com/new
2. **Repository name**：建议 `math-proof-problems` 或 `阶段性opensource`
3. **Description**：`AI辅助求解与形式化证明的数学竞赛习题集`
4. 选择 **Public**
5. **不要**勾选 "Add a README file"（本地已有）
6. 点击 **Create repository**

---

## 第四步：关联远程仓库并推送

创建仓库后，GitHub 会显示命令。在项目目录下执行（将 `仓库名` 替换为你创建的仓库名）：

```bash
git remote add origin https://github.com/ml1301215/仓库名.git
git branch -M main
git push -u origin main
```

**示例**（若仓库名为 `math-proof-problems`）：

```bash
git remote add origin https://github.com/ml1301215/math-proof-problems.git
git branch -M main
git push -u origin main
```

---

## 推送时如需登录

- **HTTPS**：会提示输入 GitHub 用户名和密码；密码需使用 [Personal Access Token](https://github.com/settings/tokens)
- **SSH**：若已配置 SSH 密钥，可将 `https://` 改为 `git@github.com:`

---

## 完成后

项目将出现在：`https://github.com/ml1301215/你的仓库名`
